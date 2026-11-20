"""sys.path setup for the provenance scripts: task solution/, tests/, provenance lib/ and alternatives/."""
import sys
from pathlib import Path
PROV = Path(__file__).resolve().parents[1]
TESTS = PROV.parent
TASK = TESTS.parent
for p in (TASK / "solution", TESTS, PROV / "lib", PROV / "alternatives"):
    if str(p) not in sys.path:
        sys.path.insert(0, str(p))
HELDOUT = TESTS / "heldout_walks.json"
EXPECTED = TESTS / "expected.json"
EXAMPLES = TASK / "environment" / "examples.json"
EXAMPLES_OUT = TASK / "environment" / "examples_output.json"
