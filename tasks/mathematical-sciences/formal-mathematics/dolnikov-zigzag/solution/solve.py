"""Oracle for dolnikov-zigzag.

Reads the starter project in /app, checks that the goal and the definitions are the ones the
proof library was written for, installs the library modules, derives the proof of the goal
from the parsed theorem statement, builds the project and audits the axioms of the result.

The proof library (/solution/proof_library/*.lean) is the Lean source of the argument:
Ky Fan's parity lemma for alternating chains of the cross-polytope (FanLabels, FanTucker,
FanStep), the antipodal labelling built from the colouring (Lab), the extraction of the
zig-zag from an alternating chain (Extract) and the assembled theorem `zigzag_main` (Main).
"""
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


def main():
    goal_path = APP / "Zigzag" / "Goal.lean"
    goal = goal_path.read_text()
    check_defs((APP / "Zigzag" / "Defs.lean").read_text())
    sig, names = parse_goal(goal)
    check_statement(sig)

    for mod in MODULES:
        shutil.copyfile(LIB / f"{mod}.lean", APP / "Zigzag" / f"{mod}.lean")

    proof = "exact zigzag_main " + " ".join(names)
    new_goal = goal.replace("import Zigzag.Defs\n", "import Zigzag.Defs\nimport Zigzag.Main\n", 1)
    new_goal = re.sub(r"(:=\s*by\s*\n\s*)sorry\b", lambda m: m.group(1) + proof, new_goal, count=1)
    goal_path.write_text(new_goal)

    r = subprocess.run(["lake", "build", "Zigzag"], cwd=APP, capture_output=True, text=True)
    print(r.stdout[-4000:])
    if r.returncode != 0 or "declaration uses" in r.stdout + r.stderr:
        fail("lake build failed or a declaration uses sorry:\n" + (r.stdout + r.stderr)[-4000:])

    probe = APP / "OracleAxioms.lean"
    probe.write_text("import Zigzag.Goal\n#print axioms Zigzag.dolnikov_zigzag\n")
    try:
        r = subprocess.run(["lake", "env", "lean", probe.name], cwd=APP, capture_output=True, text=True)
    finally:
        probe.unlink(missing_ok=True)
    out = r.stdout + r.stderr
    m = re.search(r"depends on axioms: \[(.*?)\]", out, re.S)
    if r.returncode != 0 or not m:
        fail("axiom report failed:\n" + out[-2000:])
    axioms = {a.strip() for a in m.group(1).split(",") if a.strip()}
    if not axioms <= ALLOWED_AXIOMS:
        fail(f"disallowed axioms: {sorted(axioms - ALLOWED_AXIOMS)}")
    print(f"oracle: Zigzag.dolnikov_zigzag proved; axioms {sorted(axioms)}")


if __name__ == "__main__":
    main()
