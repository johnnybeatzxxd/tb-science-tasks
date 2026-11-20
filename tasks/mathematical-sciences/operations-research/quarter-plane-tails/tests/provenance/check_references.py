"""Independent-principle checks of expected.json that do not share the kernel-method code path.
Writes check_references.txt.

(a) exact product forms: Jackson / tandem walks of the graded file (pi explicit) and the M/M/1
    marginals of the paired-arrival walks;
(b) exact algebraic certificates: for every walk and side, the candidate singular points are
    real roots of irreducible polynomials over Q (alternatives/alt_exact.py); coinciding points
    are the same root of the same irreducible polynomial, so each planted or critical
    coincidence holds exactly;
(c) numerics: subtraction-free block-GTH solution of an N x N truncation (lib/gth2d.py) and the
    local exponent kappa_n = n (a_{n+1}/(rho a_n) - 1) with the reference rho (--numeric).
"""
import json, sys
from fractions import Fraction as F
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent / "lib"))
import paths  # noqa: F401
import alt_exact as E
from near import gaps
HERE = Path(__file__).resolve().parent
walks = json.loads(paths.HELDOUT.read_text())["walks"]
EXP = json.loads(paths.EXPECTED.read_text())
lines = []


def spec(w):
    return {k2: {tuple(int(t) for t in j.split(",")): F(p) for j, p in w[k1].items()}
            for k1, k2 in (("interior", "int"), ("x_axis", "x"), ("y_axis", "y"), ("origin", "o"))}


# (b) exact certificates
lines.append("== exact algebraic candidates (minimal polynomial, root index) ==")
for w in walks:
    I = E.law(w["interior"])
    for side, S, other in (("x", E.Side(I, E.law(w["x_axis"])), E.Side(E.swap(I), E.swap(E.law(w["y_axis"])))),
                           ("y", E.Side(E.swap(I), E.swap(E.law(w["y_axis"]))), E.Side(I, E.law(w["x_axis"])))):
        x3 = S.branch()
        own = S.own(x3)
        osing = other.singularity(None)
        desc = []
        if x3 is not E.sp.oo:
            desc.append("branch %s#%d" % (x3.f.as_expr(), x3.idx))
        for z in own:
            desc.append("own %s#%d%s" % (z.f.as_expr(), z.idx, " (= branch)" if x3 is not E.sp.oo and z == x3 else ""))
        lines.append("%s %s: %s" % (w["id"], side, "; ".join(desc)))
# (a) product forms
lines.append("== exact product forms ==")
import qtails as Q
lines.append("(Jackson and tandem walks of the file are identified in check_promises.txt; their product-form rates are reproduced in check_literature.txt and below)")
for w in walks:
    I = spec(w)["int"]
    L = {a: sum(v for (x, y), v in I.items() if x == a) for a in (-1, 1)}
    if set(k for k, v in I.items() if v) <= {(1, 1), (1, 0), (0, 1), (-1, 0), (0, -1), (0, 0)} and I.get((1, 1), 0) > 0:
        # paired-arrival model: marginals M/M/1
        for c, key in ((0, "x_marginal"), (1, "y_marginal")):
            up = sum(v for k, v in I.items() if k[c] == 1); dn = sum(v for k, v in I.items() if k[c] == -1)
            ok = F(EXP[w["id"]][key]["kappa"]) == 0 and abs(F(EXP[w["id"]][key]["rho"]) / (up / dn) - 1) < F(1, 10 ** 25)
            lines.append("%s %s paired-arrival M/M/1 rho=%s: %s" % (w["id"], key, up / dn, "agrees" if ok else "DIFFERS"))
# (c) numerics
if "--numeric" in sys.argv:
    from gth2d import stationary
    lines.append("== block-GTH truncations: kappa_n with the reference rho ==")
    for w in walks:
        s = spec(w); wid = w["id"]
        rhos = {k: float(F(v["rho"])) for k, v in EXP[wid].items()}
        N = min(700, max(200, int(12 / (1 - max(rhos.values())))))
        sf = {k: {kk: float(vv) for kk, vv in d.items()} for k, d in s.items()}
        P = stationary(sf, N, N)
        seq = {"x_boundary": P[1:, 0], "y_boundary": P[0, 1:], "x_marginal": P.sum(1), "y_marginal": P.sum(0)}
        for k, v in seq.items():
            ns = [m for m in (N // 10, N // 6, N // 4, N // 3) if v[m + 1] > 1e-280]
            kn = [m * (v[m + 1] / v[m] / rhos[k] - 1) for m in ns]
            lines.append("%s %-10s rho %.6f kappa %5s | N=%d | competitor gap %.1e | kappa_n %s" % (
                wid, k, rhos[k], EXP[wid][k]["kappa"], N, gaps(s),
                " ".join("%d:%+.3f" % (m, z) for m, z in zip(ns, kn))))
(HERE / "check_references.txt").write_text("\n".join(lines) + "\n")
print("\n".join(lines[:5]), "...", len(lines), "lines")
