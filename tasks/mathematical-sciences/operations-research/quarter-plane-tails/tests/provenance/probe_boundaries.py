"""Boundary probes (R20/R32/R58): inputs at the edges of what the instruction allows must run
through the reference solver without error, give 0 < rho < 1 and rational kappa, and agree with
the exact-arithmetic alternative. Writes probe_boundaries.txt."""
import sys
from fractions import Fraction as F
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent / "lib"))
import paths  # noqa: F401
import qtails as Q, alt_exact
from models import tandem, coupled_processors, two_demand, jackson
HERE = Path(__file__).resolve().parent


def wj(s, wid):
    return {"id": wid, **{k1: {"%d,%d" % k: str(v) for k, v in s[k2].items() if v}
                           for k1, k2 in (("interior", "int"), ("x_axis", "x"), ("y_axis", "y"), ("origin", "o"))}}


probes = {
    "interior support 4 (paired arrivals only)": two_demand(0, 0, 1, 5, 5),
    "interior support 4, light traffic (rho 0.1)": two_demand(0, 0, 1, 10, 10),
    "heavy traffic rho 0.99 (tandem)": tandem(1, F(100, 99), F(100, 98)),
    "heavy traffic rho 0.98 both stations (Jackson)": jackson(1, 1, F(102, 100) * 2, F(102, 100) * 2, F(1, 2), F(1, 2)),
    "interior mean (+,-) (coupled processors, overloaded queue 1)": coupled_processors(2, 1, 1, 3, 5, 4),
    "interior mean (-,+) (coupled processors, overloaded queue 2)": coupled_processors(1, 2, 3, 1, 4, 5),
    "large denominators (rates with 7-digit denominators)": coupled_processors(F(1234567, 1000003), F(7654321, 9999991), F(3), F(4), F(5), F(6)),
    "single-jump boundary laws": tandem(1, 2, 3),
}
lines, ok = [], True
for name, s in probes.items():
    w = wj(s, "p")
    try:
        a = Q.fmt(Q.analyse(Q.parse_walk(w))); b = alt_exact.solve(w)
        good = all(0 < F(a[k]["rho"]) < 1 and a[k]["kappa"] == b[k]["kappa"] and
                   abs(F(a[k]["rho"]) / F(b[k]["rho"]) - 1) < F(1, 10 ** 20) for k in a)
        lines.append("%-62s %s %s" % (name, "ok" if good else "DISAGREE", {k: (a[k]["rho"][:10], a[k]["kappa"]) for k in a}))
    except Exception as exc:
        good = False; lines.append("%-62s ERROR %r" % (name, exc))
    ok &= good
lines.append("ALL PROBES OK" if ok else "SOME PROBE FAILED")
(HERE / "probe_boundaries.txt").write_text("\n".join(lines) + "\n"); print("\n".join(lines))
sys.exit(0 if ok else 1)
