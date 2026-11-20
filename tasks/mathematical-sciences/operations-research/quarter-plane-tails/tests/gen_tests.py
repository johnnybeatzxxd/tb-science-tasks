"""Writes tests/test_outputs.py: the runner and contract test, followed by one plain test
function per walk of tests/heldout_walks.json (no parametrisation).

usage: python3 gen_tests.py   (run from the tests/ directory)
"""
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
HEAD = (HERE / "test_outputs_head.py").read_text()
ids = [w["id"] for w in json.loads((HERE / "heldout_walks.json").read_text())["walks"]]
parts = [HEAD.rstrip() + "\n"]
for wid in ids:
    parts.append('''

def test_{wid}():
    """Walk {wid}: for all four sequences, kappa equals the exact value and rho is within
    relative error 1e-9 of the exact value, with both fields well formed."""
    ok, probs = walk_verdict("{wid}")
    assert ok, "walk {wid}: " + "; ".join(probs)
'''.format(wid=wid))
(HERE / "test_outputs.py").write_text("".join(parts))
print("wrote", len(ids), "walk tests")
