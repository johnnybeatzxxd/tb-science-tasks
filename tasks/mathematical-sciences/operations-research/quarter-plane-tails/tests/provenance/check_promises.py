"""Asserts, on the 31 graded walks (tests/heldout_walks.json) and their reference values, every
property the instruction states about the inputs and the additional file.
Writes check_promises.txt next to this script; exit status 1 if any assertion fails."""
import json, re, sys
from collections import deque
from fractions import Fraction as F
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent / "lib"))
import paths  # noqa: F401
import qtails as Q
from near import gaps
from models import jackson, tandem, coupled_processors, two_demand
import alt_exact

HERE = Path(__file__).resolve().parent
raw = json.loads(paths.HELDOUT.read_text())
walks = raw["walks"]
EXP = json.loads(paths.EXPECTED.read_text())
REG = {"interior": {(a, b) for a in (-1, 0, 1) for b in (-1, 0, 1)},
       "x_axis": {(a, b) for a in (-1, 0, 1) for b in (0, 1)},
       "y_axis": {(a, b) for a in (0, 1) for b in (-1, 0, 1)},
       "origin": {(a, b) for a in (0, 1) for b in (0, 1)}}
log = []


def check(cond, msg):
    log.append(("OK   " if cond else "FAIL ") + msg)
    return cond


def drift(law):
    return (sum(a * p for (a, b), p in law.items()), sum(b * p for (a, b), p in law.items()))


def spec(w):
    return {k2: {tuple(int(t) for t in j.split(",")): F(p) for j, p in w[k1].items()}
            for k1, k2 in (("interior", "int"), ("x_axis", "x"), ("y_axis", "y"), ("origin", "o"))}


def strongly_connected_box(s, n=24, core=8):
    def law(i, j):
        return s["int"] if i and j else s["x"] if i else s["y"] if j else s["o"]
    def nbrs(i, j, rev=False):
        out = []
        if not rev:
            for (a, b), p in law(i, j).items():
                if p and 0 <= i + a <= n and 0 <= j + b <= n:
                    out.append((i + a, j + b))
        return out
    fw = {(0, 0)}; dq = deque([(0, 0)])
    while dq:
        u = dq.popleft()
        for v in nbrs(*u):
            if v not in fw:
                fw.add(v); dq.append(v)
    radj = {}
    for i in range(n + 1):
        for j in range(n + 1):
            for v in nbrs(i, j):
                radj.setdefault(v, []).append((i, j))
    bw = {(0, 0)}; dq = deque([(0, 0)])
    while dq:
        u = dq.popleft()
        for v in radj.get(u, []):
            if v not in bw:
                bw.add(v); dq.append(v)
    box = {(i, j) for i in range(core + 1) for j in range(core + 1)}
    return box <= fw and box <= bw


ok = True
ok &= check(set(raw) == {"walks"} and isinstance(walks, list), "top level is {'walks': [...]}")
ok &= check(len(walks) == 31, "exactly 31 walks")
ids = [w["id"] for w in walks]
ok &= check(len(set(ids)) == 31 and all(isinstance(i, str) for i in ids), "ids are unique strings")
ok &= check(all(set(w) == {"id", "interior", "x_axis", "y_axis", "origin"} for w in walks), "each walk has exactly the five keys")
pat = re.compile(r"^[1-9][0-9]*/[1-9][0-9]*$")
fmt_ok = all(pat.match(p) for w in walks for r in REG for p in w[r].values())
ok &= check(fmt_ok, "every probability is a string p/q with integers p >= 1, q >= 1")
ok &= check(all(re.match(r"^-?[01],-?[01]$", j) for w in walks for r in REG for j in w[r]), "every jump key is 'a,b' with a, b in {-1,0,1}")
ok &= check(all(tuple(int(t) for t in j.split(",")) in REG[r] for w in walks for r in REG for j in w[r]),
            "boundary laws never leave the quadrant")
ok &= check(all(sum(F(p) for p in w[r].values()) == 1 for w in walks for r in REG), "every law sums to exactly 1")
maxden = max(F(p).denominator for w in walks for r in REG for p in w[r].values())
ok &= check(maxden < 10 ** 16, "denominators below 1e16 (max %d)" % maxden)
supp = [len(w["interior"]) for w in walks]
ok &= check(min(supp) == 4 and max(supp) == 9, "interior support sizes between 4 and 9, both reached (%d..%d)" % (min(supp), max(supp)))
specs = {w["id"]: spec(w) for w in walks}
pos = 0
for wid, s in specs.items():
    mx, my = drift(s["int"]); m1 = drift(s["x"]); m2 = drift(s["y"])
    I = s["int"]
    ok &= check(mx != 0 and my != 0, "%s interior mean nonzero in both coordinates" % wid)
    ok &= check(all(any(p > 0 and k[c] == sg for k, p in I.items()) for c in (0, 1) for sg in (-1, 1)),
                "%s interior law has an increasing and a decreasing jump in each coordinate" % wid)
    c1 = mx * m1[1] - my * m1[0] < 0; c2 = my * m2[0] - mx * m2[1] < 0
    erg = (c1 and c2) if (mx < 0 and my < 0) else c1 if (mx > 0 and my < 0) else c2 if (mx < 0 and my > 0) else False
    ok &= check(erg, "%s positive recurrent (Fayolle-Malyshev-Menshikov drift conditions)" % wid)
    ok &= check(strongly_connected_box(s), "%s irreducible (origin reaches and is reached from every state of [0,8]^2 within [0,24]^2)" % wid)
    loops = any(s[r].get((0, 0), 0) > 0 for r in ("int", "x", "y", "o"))
    ok &= check(loops, "%s aperiodic (a law has a self-loop)" % wid)
    pos += (mx > 0) or (my > 0)
ok &= check(pos == 12, "12 walks with one positive interior mean component (%d)" % pos)
rhos = [F(v["rho"]) for a in EXP.values() for v in a.values()]
ok &= check(min(rhos) == F("0.1875") and abs(max(rhos) - F("0.98")) < F(1, 10 ** 25), "exact rho between 0.1875 and 0.98, both reached")
ok &= check(all(0 < r < 1 for r in rhos), "0 < rho < 1")
ok &= check(all(F(v["kappa"]).denominator in (1, 2) for a in EXP.values() for v in a.values()), "kappa rational")
# classical networks at natural rational rates: rebuild them and find them in the file
def jr(l1, l2, r12, r21, a, b):
    l1, l2, r12, r21 = map(F, (l1, l2, r12, r21))
    L1 = (l1 + l2 * r21) / (1 - r12 * r21); L2 = (l2 + l1 * r12) / (1 - r12 * r21)
    return jackson(l1, l2, L1 / F(a), L2 / F(b), r12, r21)
models = {"Jackson network with feedback": jr(3, 2, F(1, 2), F(1, 4), F(3, 5), F(7, 10)),
          "Jackson network, heavy traffic": jr(2, 1, F(1, 3), F(1, 5), F(49, 50), F(24, 25)),
          "tandem network": tandem(1, F(9, 4), F(3, 2)),
          "tandem network, heavy traffic": tandem(1, F(50, 49), F(25, 24)),
          "coupled processors (2,3,6,9,11,4)": coupled_processors(2, 3, 6, 9, 11, 4),
          "coupled processors (4,2,6,7,12,6)": coupled_processors(4, 2, 6, 7, 12, 6),
          "coupled processors (5,3,4,4,14,5)": coupled_processors(5, 3, 4, 4, 14, 5),
          "parallel queues, paired arrivals only (0,0,1,5,5)": two_demand(0, 0, 1, 5, 5),
          "parallel queues (1,1,2,9,7)": two_demand(1, 1, 2, 9, 7),
          "parallel queues (3,0,4,8,5)": two_demand(3, 0, 4, 8, 5),
          "parallel queues (4,4,1,6,11)": two_demand(4, 4, 1, 6, 11),
          "parallel queues (2,3,1,10,6)": two_demand(2, 3, 1, 10, 6),
          "parallel queues, heavy traffic": two_demand(1, 2, 2, F(31, 10), F(41, 10))}
norm = lambda s: {r: {k: v for k, v in d.items() if v} for r, d in s.items()}
filespecs = {wid: norm(s) for wid, s in specs.items()}
for name, m in models.items():
    hit = [wid for wid, s in filespecs.items() if s == norm(m)]
    ok &= check(len(hit) == 1, "classical network present: %s -> %s" % (name, hit))
# exact regime boundaries: coincident singular points, decided exactly by alt_exact
exact_cases = 0
for w in walks:
    kap = [F(v["kappa"]) for v in EXP[w["id"]].values()]
    if any(k in (F(-1, 2), F(1)) for k in kap):
        exact_cases += 1
ok &= check(exact_cases >= 10, "walks on an exact regime boundary (kappa -1/2 or 1 somewhere): %d" % exact_cases)
gs = {wid: gaps(s) for wid, s in specs.items()}
near = sorted(g for g in gs.values() if g < 1e-3)
ok &= check(len(near) == 10 and near[0] >= 3e-5, "10 near-coincidences with relative distance in [3e-5, 1e-3): %s" % ["%.2e" % g for g in near])
# all three solvers agree with expected
for w in walks:
    a = Q.fmt(Q.analyse(Q.parse_walk(w))); b = alt_exact.solve(w)
    for k in a:
        same = (F(a[k]["kappa"]) == F(EXP[w["id"]][k]["kappa"]) == F(b[k]["kappa"]) and
                abs(F(a[k]["rho"]) / F(EXP[w["id"]][k]["rho"]) - 1) < F(1, 10 ** 20) and
                abs(F(b[k]["rho"]) / F(EXP[w["id"]][k]["rho"]) - 1) < F(1, 10 ** 20))
        ok &= check(same, "%s %s: reference and exact-arithmetic solver reproduce expected.json" % (w["id"], k))
log.append("ALL PROMISES HOLD" if ok else "SOME PROMISE FAILS")
(HERE / "check_promises.txt").write_text("\n".join(log) + "\n")
print("\n".join(l for l in log if not l.startswith("OK")) or "all OK", len(log))
sys.exit(0 if ok else 1)
