"""Verifier for dolnikov-zigzag.

The submission is the directory /app/Zigzag/ (declared artifact). The verifier owns every
other file of the Lean project (lakefile, manifest, toolchain, root module, Defs.lean) and
the Mathlib build baked into this image. Checks, in order:

1. contract: Goal.lean exists and every submitted file is a regular `.lean` file;
2. source scan: no submitted file contains a construct that runs submitted code at build or
   load time or that bypass the kernel (#eval, run_cmd, macros, elaborators, simprocs,
   initializers, native_decide, set_option debug.*, skipKernelTC,
   implemented_by/extern, metaprogramming monads, IO);
3. build: canonical files are restored, the agent's build directory is wiped, and the
   package is re-elaborated from source with no `sorry` warning;
4. statement pin: the submitted constant is checked against ZigzagSpec.Statement, the statement
   elaborated in a verifier-owned module that does not import the submission, derives a
   held-out Petersen-graph (KG(5,2)) zig-zag instance, and checks that the data-part theorem
   `Zigzag.family_chromatic_number` states the true chromatic number of the Kneser graph of
   data/family.json, which the verifier computes itself as a minimum cover of the vertices
   by maximal independent sets (Bron–Kerbosch), independently of the oracle's method;
5. axiom audit: the kernel environment is traversed from both theorems and the verifier's
   pins; the axioms reached must be a subset of {propext, Classical.choice, Quot.sound};
6. kernel re-check: every submitted theorem and definition reachable from those roots is
   re-added to the environment with kernel type checking enabled.
"""
import filecmp
import functools
import itertools
import json
import operator
import re
import shutil
import subprocess
import time
from pathlib import Path

APP = Path("/app")
SUB = APP / "Zigzag"
TESTS = Path("/tests")
SEED = TESTS / "seed"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
CANONICAL = [
    ("lakefile.toml", "lakefile.toml"),
    ("lake-manifest.json", "lake-manifest.json"),
    ("lean-toolchain", "lean-toolchain"),
    ("Zigzag.lean", "Zigzag.lean"),
    ("Zigzag/Defs.lean", "Zigzag/Defs.lean"),
    ("ZigzagSpec.lean", "ZigzagSpec.lean"),
]
ROOTS = ["Zigzag.dolnikov_zigzag", "ZigzagCheck.pin", "ZigzagCheck.petersen_zigzag",
         "Zigzag.family_chromatic_number", "ZigzagCheck.family_pin"]


TOTAL_BUDGET_SEC = 1200  # the instruction: the whole verification must finish within this
_started = []


def family_sets():
    """The set system of data/family.json (verifier copy), checked against `family` in Defs.lean."""
    d = json.loads((SEED / "data" / "family.json").read_text())
    n, sets = d["n"], sorted(sorted(S) for S in d["sets"])
    defs = (SEED / "Zigzag" / "Defs.lean").read_text()
    m = re.search(r"def\s+family\s*:\s*Finset \(Finset \(Fin (\d+)\)\)\s*:=\s*\{(.*?)\}\s*\n", defs, re.S)
    assert m and int(m.group(1)) == n, "verifier data: Defs.lean has no family over the same ground set"
    lean_sets = sorted(sorted(int(x) for x in g.split(",")) for g in re.findall(r"\{([0-9, ]+)\}", m.group(2)))
    assert lean_sets == sets, "verifier data: family.json and Defs.lean disagree"
    return n, sets


def true_chromatic_number():
    """Reference value: the chromatic number of the Kneser graph of the family, computed as a
    minimum cover by maximal independent sets (a method independent of the oracle's search).

    Vertices are the members of the family, adjacent iff disjoint, so the independent sets are
    the pairwise-intersecting subfamilies. Bron–Kerbosch on the intersection graph lists all
    maximal ones; every colour class lies in one of them, so the chromatic number is the least
    k such that some k maximal independent sets cover all vertices (checked exhaustively)."""
    _, sets = family_sets()
    masks = [sum(1 << i for i in S) for S in sets]
    m = len(masks)
    inter = [sum(1 << j for j in range(m) if j != i and masks[i] & masks[j]) for i in range(m)]
    maximal = []

    def bron_kerbosch(r, p, x):
        if p == 0 and x == 0:
            maximal.append(r)
            return
        u = (p | x).bit_length() - 1
        for v in [v for v in range(m) if p >> v & 1 and not inter[u] >> v & 1]:
            bron_kerbosch(r | 1 << v, p & inter[v], x & inter[v])
            p &= ~(1 << v)
            x |= 1 << v

    bron_kerbosch(0, (1 << m) - 1, 0)
    full = (1 << m) - 1
    k = 1
    while not any(functools.reduce(operator.or_, c) == full for c in itertools.combinations(maximal, k)):
        k += 1
    return k


def check_source():
    """Check.lean with the family pin instantiated at the verifier's own reference value."""
    k = true_chromatic_number()
    numeral = "Nat.zero"
    for _ in range(k):
        numeral = f"Nat.succ ({numeral})"
    return (TESTS / "Check.lean").read_text().replace("__FAMILY_K__", numeral)


def run(cmd):
    """Run a Lean command; all commands together must fit in TOTAL_BUDGET_SEC."""
    if not _started:
        _started.append(time.monotonic())
    remaining = TOTAL_BUDGET_SEC - (time.monotonic() - _started[0])
    assert remaining > 0, f"the verification exceeded {TOTAL_BUDGET_SEC} seconds"
    try:
        return subprocess.run(cmd, cwd=APP, capture_output=True, text=True, timeout=remaining)
    except subprocess.TimeoutExpired:
        raise AssertionError(f"the verification exceeded {TOTAL_BUDGET_SEC} seconds")


def submitted_files():
    return sorted(p for p in SUB.rglob("*") if not p.is_dir())


def submitted_lean():
    return [p for p in submitted_files() if p.suffix == ".lean"]


def strip_comments(txt):
    """Remove Lean block and line comments so that banned words in comments are ignored."""
    out, i, depth = [], 0, 0
    while i < len(txt):
        if txt.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and txt.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif txt.startswith("--", i):
            j = txt.find("\n", i)
            i = len(txt) if j < 0 else j
        else:
            out.append(txt[i])
            i += 1
    return "".join(out)


BANNED = [
    # Constructs that execute submitted code while the verifier compiles or loads the
    # submission (such code could read or rewrite verifier files or forge reports).
    # Soundness is not enforced here: `sorry`, axioms and kernel bypasses are caught by
    # the build, the axiom audit and the kernel re-check.
    (r"(?m)^\s*#(?:eval|exit)\b", "#eval/#exit"),
    (r"\b(?:run_cmd|run_elab|run_meta|run_tac)\b", "run_cmd/run_elab/run_meta/run_tac"),
    (r"(?m)^\s*(?:@\[[^\]]*\]\s*|(?:private|protected|scoped|local)\s+|open\b[^\n]*?\bin\s+)*(?:macro_rules|macro|elab_rules|elab|initialize|builtin_initialize|simproc|dsimproc)\b", "macro/elab/initialize/simproc command"),
    (r"\bnative_decide\b|\bdecide\s*\+\s*native\b", "native_decide (runs compiled code)"),
    (r"\bset_option\s+debug\.|\bskipKernelTC\b", "kernel-bypass option (set_option debug.*, skipKernelTC)"),
    (r"(?:@\[|\battribute\s*\[)[^\]]*\b(?:implemented_by|extern|init|builtin_init)\b", "implemented_by/extern/init attribute"),
    (r"\b(?:IO|BaseIO|EIO|unsafeBaseIO|unsafeIO|unsafeEIO|unsafePerformIO|MetaM|TacticM|CoreM|TermElabM|CommandElabM|SimpM|addDecl|addDeclCore|setEnv|modifyEnv|ofReduceBool|trustCompiler|FilePath)\b", "metaprogramming or system access"),
    (r"(?m)^(?!\s*import\b).*?\b(?:Lean|Mathlib)\.(?:Meta|Elab|Tactic|Compiler|Environment)\b", "metaprogramming namespace"),
]


def test_artifact_contract():
    """Goal.lean exists and every file in the submission directory is a regular (non-symlink) .lean file."""
    assert SUB.is_dir(), "/app/Zigzag/ is missing"
    goal = SUB / "Goal.lean"
    assert goal.is_file() and not goal.is_symlink(), "/app/Zigzag/Goal.lean is missing"
    for p in SUB.rglob("*"):
        assert not p.is_symlink(), f"symlink in submission: {p}"
        if not p.is_dir():
            assert p.is_file(), f"not a regular file in submission: {p}"
            assert p.suffix == ".lean", f"non-Lean file in submission: {p}"


def test_no_banned_constructs():
    """No submitted file contains a command or attribute that executes code while the verifier builds or loads it."""
    for f in submitted_lean():
        txt = strip_comments(f.read_text(errors="replace"))
        for pat, name in BANNED:
            m = re.search(pat, txt)
            assert not m, f"banned construct ({name}) in {f}: {m.group(0)!r}"


def test_build_from_source():
    """With the canonical project files restored and the agent's build wiped, the package builds from source without `sorry`."""
    for src, dst in CANONICAL:
        (APP / dst).parent.mkdir(parents=True, exist_ok=True)
        shutil.copy(SEED / src, APP / dst)
    (APP / "lakefile.lean").unlink(missing_ok=True)
    shutil.rmtree(APP / ".lake" / "build", ignore_errors=True)
    r = run(["lake", "build", "Zigzag", "ZigzagSpec"])
    out = r.stdout + r.stderr
    assert r.returncode == 0, f"lake build failed:\n{out[-6000:]}"
    assert "declaration uses" not in out, "the build reports a declaration using sorry"
    for src, dst in CANONICAL:
        assert filecmp.cmp(SEED / src, APP / dst, shallow=False), f"{dst} differs from the canonical copy"


def test_statement_pin_and_instance():
    """The theorem has exactly the stated type and yields a held-out Petersen-graph (KG(5,2)) zig-zag instance, and the data-part theorem states the true chromatic number of the Kneser graph of `family`, which the verifier computes itself from data/family.json as a minimum cover by maximal independent sets."""
    (APP / "Check.lean").write_text(check_source())
    r = run(["lake", "env", "lean", "Check.lean"])
    assert r.returncode == 0, f"statement pin / held-out instance failed:\n{(r.stdout + r.stderr)[-6000:]}"


def test_axioms():
    """The theorem and the held-out instance depend only on propext, Classical.choice and Quot.sound."""
    roots = ", ".join(f"`{x}" for x in ROOTS)
    script = check_source() + f"""
open Lean in
partial def axCollect (env : Environment) : List Name → NameSet → NameSet → NameSet
  | [], _, axs => axs
  | n :: rest, vis, axs =>
    if vis.contains n then axCollect env rest vis axs
    else
      let vis := vis.insert n
      match env.find? n with
      | none => axCollect env rest vis axs
      | some ci =>
        let axs := if ci matches .axiomInfo _ then axs.insert n else axs
        let deps := (ci.type.getUsedConstants ++
          (match ci.value? (allowOpaque := true) with | some v => v.getUsedConstants | none => #[])).toList
        axCollect env (deps ++ rest) vis axs

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let roots : List Name := [{roots}]
  for r in roots do
    if (env.find? r).isNone then throwError "missing root constant {{r}}"
  let mut axs := axCollect env roots {{}} {{}}
  for r in roots do
    for a in (← Lean.collectAxioms r) do
      axs := axs.insert a
  IO.println "<<axioms-begin>>"
  for a in axs.toList do IO.println a.toString
  IO.println "<<axioms-end>>"
"""
    (APP / "AxiomCheck.lean").write_text(script)
    r = run(["lake", "env", "lean", "AxiomCheck.lean"])
    assert r.returncode == 0, f"axiom traversal failed:\n{(r.stdout + r.stderr)[-6000:]}"
    blocks = re.findall(r"<<axioms-begin>>\n(.*?)<<axioms-end>>", r.stdout, re.S)
    assert len(blocks) == 1, f"expected one axiom report, got {len(blocks)}"
    found = {line.strip() for line in blocks[0].splitlines() if line.strip()}
    assert found <= ALLOWED_AXIOMS, f"disallowed axioms: {sorted(found - ALLOWED_AXIOMS)}"


def test_kernel_recheck():
    """Every submitted theorem and definition reachable from the theorem is re-added to the environment and re-checked by the Lean kernel (inductive types are kernel-checked when the build adds them, and kernel-bypass options are banned)."""
    roots = ", ".join(f"`{x}" for x in ROOTS)
    script = check_source() + f"""
open Lean in
partial def rkCollect (env : Environment) : List Name → NameSet → NameSet
  | [], s => s
  | n :: rest, s =>
    if s.contains n then rkCollect env rest s
    else
      let s := s.insert n
      match env.find? n with
      | none => rkCollect env rest s
      | some ci =>
        let deps := (ci.type.getUsedConstants ++
          (match ci.value? (allowOpaque := true) with | some v => v.getUsedConstants | none => #[])).toList
        rkCollect env (deps ++ rest) s

open Lean in
def rkSubmitted (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => (env.header.moduleNames[idx.toNat]!).toString.startsWith "Zigzag"
  | none => false

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let roots : List Name := [{roots}]
  let hb := (Core.getMaxHeartbeats (← getOptions)).toUSize
  let rd := (maxRecDepth.get (← getOptions)).toUSize
  let mut count := 0
  for c in (rkCollect env roots {{}}).toList do
    if rkSubmitted env c then
      match env.find? c with
      | some (.thmInfo v) =>
        match env.addDeclCore hb rd (.thmDecl {{ v with name := c.appendAfter "__rk" }}) none true with
        | .ok _ => count := count + 1
        | .error _ => throwError "kernel re-check failed for {{c}}"
      | some (.defnInfo v) =>
        match env.addDeclCore hb rd (.defnDecl {{ v with name := c.appendAfter "__rk" }}) none true with
        | .ok _ => count := count + 1
        | .error _ => throwError "kernel re-check failed for {{c}}"
      | some (.inductInfo _) | some (.ctorInfo _) | some (.recInfo _) => pure ()
      | some _ => throwError "declaration {{c}} is not a theorem, definition or inductive type"
      | none => pure ()
  IO.println s!"<<recheck-ok {{count}}>>"
"""
    (APP / "KernelCheck.lean").write_text(script)
    r = run(["lake", "env", "lean", "KernelCheck.lean"])
    assert r.returncode == 0, f"kernel re-check failed:\n{(r.stdout + r.stderr)[-6000:]}"
    m = re.search(r"<<recheck-ok (\d+)>>", r.stdout)
    assert m, "kernel re-check did not report"
    assert int(m.group(1)) >= 1, "kernel re-check found no submitted declaration to check"
