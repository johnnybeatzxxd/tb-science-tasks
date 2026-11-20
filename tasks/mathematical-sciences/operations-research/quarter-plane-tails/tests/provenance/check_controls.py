"""Negative controls for the output checker: every control output must be judged incorrect by
the same code the verifier uses (qtails_check.py), and the reference output must be correct.
Writes check_controls.txt next to this script."""
import json, sys
from fractions import Fraction
from decimal import Decimal, getcontext
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent / "lib"))
import paths  # noqa: F401
import qtails_check as QC
import qtails
getcontext().prec = 50
HERE = Path(__file__).resolve().parent
walks = json.loads(paths.HELDOUT.read_text())["walks"]
ids = [w["id"] for w in walks]
EXP = json.loads(paths.EXPECTED.read_text())


def verdict(raw: bytes):
    try:
        data = QC.parse_strict(raw)
    except Exception as exc:
        return False, "rejected by strict parser: %s" % exc
    st = QC.check_structure(data, ids)
    bad = [w for w in ids if not QC.judge_walk(data, w, EXP[w])[0]]
    ok = not st and not bad
    return ok, "structure problems %d, incorrect walks %d" % (len(st), len(bad))


ref = {w["id"]: qtails.fmt(qtails.analyse(qtails.parse_walk(w))) for w in walks}
dump = lambda d: json.dumps(d).encode()
controls = {}
controls["reference output (must be correct)"] = dump(ref)
controls["empty file"] = b""
controls["empty object"] = b"{}"
controls["copy of the public example output"] = paths.EXAMPLES_OUT.read_bytes()
d = json.loads(json.dumps(ref)); w = d[ids[7]]["x_marginal"]; w["rho"] = str(Decimal(w["rho"]) * (1 + Decimal("1.01e-9")))
controls["one rho just past tolerance (x 1+1.01e-9)"] = dump(d)
d = json.loads(json.dumps(ref)); w = d[ids[7]]["x_marginal"]; w["rho"] = str(Decimal(w["rho"]) * (1 + Decimal("0.99e-9")))
controls["one rho just inside tolerance (x 1+0.99e-9, must be correct)"] = dump(d)
d = json.loads(json.dumps(ref)); del d[ids[-1]]
controls["one walk dropped"] = dump(d)
d = json.loads(json.dumps(ref)); d["w99"] = d[ids[0]]
controls["spurious extra walk id"] = dump(d)
d = json.loads(json.dumps(ref)); d[ids[2]]["y_boundary"]["kappa"] = str(Fraction(d[ids[2]]["y_boundary"]["kappa"]) + Fraction(1, 2))
controls["one kappa off by 1/2"] = dump(d)
d = json.loads(json.dumps(ref)); d[ids[0]]["x_boundary"]["rho"] = float(d[ids[0]]["x_boundary"]["rho"])
controls["rho as a JSON number"] = dump(d)
d = json.loads(json.dumps(ref)); d[ids[0]]["x_boundary"]["kappa"] = True
controls["kappa as a boolean"] = dump(d)
controls["duplicate key"] = ('{"%s": %s, ' % (ids[0], json.dumps(ref[ids[0]])) + json.dumps(ref)[1:]).encode()
controls["NaN constant"] = dump(ref).replace(b'"%s"' % ref[ids[0]]["x_boundary"]["rho"].encode(), b"NaN", 1)
d = json.loads(json.dumps(ref)); d[ids[0]]["x_boundary"]["rho"] = "%.12g" % float(d[ids[0]]["x_boundary"]["rho"])
controls["rho with 12 significant digits"] = dump(d)
for f in sorted((HERE / "controls").glob("*.json")):
    controls["weak baseline: %s" % f.stem] = f.read_bytes()
lines, allgood = [], True
for name, raw in controls.items():
    ok, why = verdict(raw)
    must = "must be correct" in name
    good = ok == must
    allgood &= good
    lines.append("%-70s %-9s %s %s" % (name, "CORRECT" if ok else "INCORRECT", "as required" if good else "UNEXPECTED", why))
lines.append("ALL CONTROLS AS REQUIRED" if allgood else "SOME CONTROL UNEXPECTED")
(HERE / "check_controls.txt").write_text("\n".join(lines) + "\n")
print("\n".join(lines))
sys.exit(0 if allgood else 1)
