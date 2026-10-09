"""Oracle for dolnikov-zigzag.

Reads the starter project in /app, checks that the goal and the definitions are the ones the
proof library was written for, installs the library modules, derives the proof of the goal
from the parsed theorem statement, builds the project and audits the axioms of the result.

For the data part it reads /app/data/family.json, computes the 2-colourability defect t of the
set system and the chromatic number k of its Kneser graph together with a proper k-colouring,
and, when t = k, writes a Lean proof of `FamilyChromaticNumber k`: the colouring gives the upper
bound, and the zig-zag theorem applied with the defect t gives the lower bound.

The proof library (/solution/proof_library/*.lean) is the Lean source of the argument:
Ky Fan's parity lemma for alternating chains of the cross-polytope (FanLabels, FanTucker,
FanStep), the antipodal labelling built from the colouring (Lab), the extraction of the
zig-zag from an alternating chain (Extract) and the assembled theorem `zigzag_main` (Main).
"""
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

APP = Path(os.environ.get("APP", "/app"))
LIB = Path(__file__).resolve().parent / "proof_library"
MODULES = ["FanLabels", "FanTucker", "FanStep", "Lab", "Extract", "Main"]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def fail(msg):
    print(f"oracle: {msg}", file=sys.stderr)
    sys.exit(1)


def norm(s):
    return " ".join(s.split())


def parse_goal(text):
    """Return (signature, binder names) of `dolnikov_zigzag` in the starter Goal.lean."""
    m = re.search(r"theorem\s+dolnikov_zigzag\s*(.*?):=\s*by\s*\n\s*sorry\b", text, re.S)
    if not m:
        fail("could not find `theorem dolnikov_zigzag ... := by sorry` in Goal.lean")
    sig = m.group(1)
    names, depth, start = [], 0, None
    for i, ch in enumerate(sig):
        if ch in "({[":
            if depth == 0:
                start = i
            depth += 1
        elif ch in ")}]":
            depth -= 1
            if depth == 0 and sig[start] == "(":
                names.append(sig[start + 1:i].split(":")[0].strip())
        elif ch == ":" and depth == 0:
            break
    if len(names) != 5:
        fail(f"expected five explicit binders in the goal, found {names}")
    return sig, names


def check_defs(text):
    m = re.search(r"def\s+Mono\s*\{n\s*:\s*ℕ\}\s*\(col\s*:\s*Fin n → Bool\)\s*\(A\s*:\s*Finset \(Fin n\)\)"
                  r"\s*:\s*Prop\s*:=\s*(.*?)\n\s*\n", text, re.S)
    if not m or norm(m.group(1)) != "∀ i ∈ A, ∀ j ∈ A, col i = col j":
        fail("Defs.lean does not define `Mono` as the proof library expects")


def check_statement(sig):
    """The statement proved by `zigzag_main` in the library must be the goal's statement."""
    main = (LIB / "Main.lean").read_text()
    m = re.search(r"theorem\s+zigzag_main\s*(.*?):=\s*by", main, re.S)
    if not m:
        fail("proof library has no `zigzag_main`")
    if norm(m.group(1)) != norm(sig.replace("{n : ℕ}", "", 1)):
        fail("the goal statement differs from the statement proved by the library")


def family_from_json():
    d = json.loads((APP / "data" / "family.json").read_text())
    return d["n"], [sorted(S) for S in d["sets"]]


def check_family_matches_defs(n, sets, defs_text):
    m = re.search(r"def\s+family\s*:\s*Finset \(Finset \(Fin (\d+)\)\)\s*:=\s*\{(.*?)\}\s*\n", defs_text, re.S)
    if not m or int(m.group(1)) != n:
        fail("Defs.lean has no `family` over the ground set of family.json")
    lean_sets = [sorted(int(x) for x in g.split(",")) for g in re.findall(r"\{([0-9, ]+)\}", m.group(2))]
    if sorted(lean_sets) != sorted(sets):
        fail("`family` in Defs.lean differs from data/family.json")


def defect(n, F):
    """Largest t such that every (D, col) with no monochromatic member of F inside D^c has |D| >= t."""
    best = n
    full = (1 << n) - 1
    for col in range(1 << n):
        for D in range(1 << n):
            pc = bin(D).count("1")
            if pc >= best:
                continue
            Dc = full & ~D
            if all(not (A & ~Dc == 0 and (A & col) in (0, A)) for A in F):
                best = pc
    return best


def colouring(F, k):
    """A proper k-colouring of the Kneser graph of F (members adjacent iff disjoint), or None."""
    m = len(F)
    adj = [[j for j in range(m) if j != i and F[i] & F[j] == 0] for i in range(m)]
    order = sorted(range(m), key=lambda i: -len(adj[i]))
    col = [-1] * m

    def bt(i):
        if i == m:
            return True
        v = order[i]
        used = {col[u] for u in adj[v] if col[u] >= 0}
        for c in range(k):
            if c not in used:
                col[v] = c
                if bt(i + 1):
                    return True
                col[v] = -1
        return False

    return list(col) if bt(0) else None


def family_proof(n, sets, k, col):
    expr = "0"
    for S, c in reversed(list(zip(sets, col))):
        expr = f"if A = {{{', '.join(map(str, S))}}} then {c} else {expr}"
    chain = "\n".join(f"  have h{i} := hinc {i} {i + 1} (by decide)" for i in range(k - 1))
    return f"""
/-- An explicit proper colouring of the Kneser graph of `family` with {k} colours. -/
def familyColour (A : Finset (Fin {n})) : Fin {k} :=
  {expr}

theorem familyColour_proper :
    ∀ A ∈ family, ∀ B ∈ family, Disjoint A B → familyColour A ≠ familyColour B := by
  decide +kernel

theorem family_nonempty : ∀ A ∈ family, A.Nonempty := by
  decide +kernel

/-- The 2-colourability defect of `family` is at least {k}. -/
theorem family_defect : ∀ (D : Finset (Fin {n})) (col : Fin {n} → Bool),
    (∀ A ∈ family, A ⊆ Dᶜ → ¬ Mono col A) → {k} ≤ D.card := by
  unfold Mono
  decide +kernel

theorem family_colorable : (kneserGraphOf family).Colorable {k} :=
  ⟨SimpleGraph.Coloring.mk (fun A => familyColour A.1) (fun {{A B}} h => by
    rw [kneserGraphOf, SimpleGraph.fromRel_adj] at h
    obtain ⟨-, h | h⟩ := h
    · exact familyColour_proper _ A.2 _ B.2 h
    · exact (familyColour_proper _ B.2 _ A.2 h).symm)⟩

/-- No proper colouring with {k - 1} colours: the zig-zag theorem with the defect bound {k}
gives {k} members of `family` with strictly increasing colours. -/
theorem family_not_colorable : ¬ (kneserGraphOf family).Colorable {k - 1} := by
  rintro ⟨C⟩
  classical
  let c : Finset (Fin {n}) → ℕ := fun A => if h : A ∈ family then (C ⟨A, h⟩ : ℕ) else 0
  have hlt : ∀ A ∈ family, c A < {k - 1} := fun A h => by
    simp only [c, h]; exact (C ⟨A, h⟩).isLt
  have hc : ∀ A ∈ family, ∀ B ∈ family, Disjoint A B → c A ≠ c B := by
    intro A hA B hB hAB hcAB
    have hne : (⟨A, hA⟩ : {{A // A ∈ family}}) ≠ ⟨B, hB⟩ := by
      intro h
      have hAB' : A = B := congrArg Subtype.val h
      subst hAB'
      obtain ⟨x, hx⟩ := family_nonempty A hA
      exact Finset.disjoint_left.1 hAB hx hx
    have hadj : (kneserGraphOf family).Adj ⟨A, hA⟩ ⟨B, hB⟩ := by
      rw [kneserGraphOf, SimpleGraph.fromRel_adj]
      exact ⟨hne, Or.inl hAB⟩
    apply C.valid hadj
    simp only [c, hA, hB, dite_true] at hcAB
    exact Fin.ext hcAB
  obtain ⟨f, hf, hinc, -⟩ := dolnikov_zigzag family c hc {k} family_defect
{chain}
  have hlast := hlt _ (hf {k - 1})
  omega

theorem family_chromatic_number : FamilyChromaticNumber {k} := by
  unfold FamilyChromaticNumber
  rw [show (({k} : ℕ) : ℕ∞) = ({k - 1} : ℕ) + 1 by norm_num,
    SimpleGraph.chromaticNumber_eq_iff_colorable_not_colorable]
  exact ⟨family_colorable, family_not_colorable⟩
"""


def main():
    goal_path = APP / "Zigzag" / "Goal.lean"
    goal = goal_path.read_text()
    check_defs((APP / "Zigzag" / "Defs.lean").read_text())
    sig, names = parse_goal(goal)
    check_statement(sig)

    n, sets = family_from_json()
    check_family_matches_defs(n, sets, (APP / "Zigzag" / "Defs.lean").read_text())
    F = [sum(1 << i for i in S) for S in sets]
    t = defect(n, F)
    k = 1
    while colouring(F, k) is None:
        k += 1
    print(f"oracle: family.json: defect t = {t}, chromatic number k = {k}")
    if t != k:
        fail("the defect bound does not match the chromatic number; this oracle needs t = k")
    family_src = family_proof(n, sets, k, colouring(F, k))

    for mod in MODULES:
        shutil.copyfile(LIB / f"{mod}.lean", APP / "Zigzag" / f"{mod}.lean")

    proof = "exact zigzag_main " + " ".join(names)
    new_goal = goal.replace("import Zigzag.Defs\n", "import Zigzag.Defs\nimport Zigzag.Main\n", 1)
    new_goal = re.sub(r"(:=\s*by\s*\n\s*)sorry\b", lambda m: m.group(1) + proof, new_goal, count=1)
    i = new_goal.rindex("end Zigzag")
    new_goal = new_goal[:i] + family_src.lstrip("\n") + "\n" + new_goal[i:]
    goal_path.write_text(new_goal)

    r = subprocess.run(["lake", "build", "Zigzag"], cwd=APP, capture_output=True, text=True)
    print(r.stdout[-4000:])
    if r.returncode != 0 or "declaration uses" in r.stdout + r.stderr:
        fail("lake build failed or a declaration uses sorry:\n" + (r.stdout + r.stderr)[-4000:])

    probe = APP / "OracleAxioms.lean"
    probe.write_text("import Zigzag.Goal\n#print axioms Zigzag.dolnikov_zigzag\n"
                     "#print axioms Zigzag.family_chromatic_number\n")
    try:
        r = subprocess.run(["lake", "env", "lean", probe.name], cwd=APP, capture_output=True, text=True)
    finally:
        probe.unlink(missing_ok=True)
    out = r.stdout + r.stderr
    reports = re.findall(r"depends on axioms: \[(.*?)\]", out, re.S)
    if r.returncode != 0 or len(reports) != 2:
        fail("axiom report failed:\n" + out[-2000:])
    axioms = {a.strip() for rep in reports for a in rep.split(",") if a.strip()}
    if not axioms <= ALLOWED_AXIOMS:
        fail(f"disallowed axioms: {sorted(axioms - ALLOWED_AXIOMS)}")
    print(f"oracle: Zigzag.dolnikov_zigzag and Zigzag.family_chromatic_number ({k}) proved; "
          f"axioms {sorted(axioms)}")


if __name__ == "__main__":
    main()
