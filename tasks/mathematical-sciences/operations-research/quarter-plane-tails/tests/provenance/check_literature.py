"""Published anchors reproduced by the reference solver (writes check_literature.txt).

1. Jackson, J. R. (1957). Networks of waiting lines. Operations Research 5(4), 518-521.
   Two-node open Jackson network with routing r12, r21: pi(n1,n2) = prod (1-rho_i) rho_i^{n_i},
   rho_i = Lambda_i/mu_i with Lambda = lambda + Lambda R. Hence all four sequences are
   geometric: rho = rho_1 (x) or rho_2 (y), kappa = 0. (Tandem networks: r12 = 1, l2 = r21 = 0.)
2. Flatto, L. and Hahn, S. (1984). Two parallel queues created by arrivals with two demands I.
   SIAM J. Appl. Math. 44(5), 1041-1053 (doi:10.1137/0144074). Each station of the
   paired-arrival model (arrivals l_i alone, l12 to both, exponential service mu_i) is an
   M/M/1 queue with arrival rate l_i + l12, so P(L_i = n) is geometric with
   rho = (l_i + l12)/mu_i and kappa = 0, whatever the boundary asymptotics.
3. Miyazawa, M. (2009). Tail decay rates in double QBD processes and related reflected random
   walks. Math. Oper. Res. 34(3), 547-575: the decay rates of the boundary distributions are
   given by the extreme points of the convex level curves (alternatives/alt_theta.py implements
   this description; the comparison is in check_references.txt).
"""
import random, sys
from fractions import Fraction as F
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent / "lib"))
import paths  # noqa: F401
import qtails as Q
from models import jackson, two_demand
HERE = Path(__file__).resolve().parent
rng = random.Random(1957); lines = []; bad = 0; nj = nf = 0
while nj < 60:
    l1, l2 = F(rng.randint(1, 30)), F(rng.randint(0, 30)); r12, r21 = F(rng.randint(0, 10), 10), F(rng.randint(0, 9), 10)
    L1 = (l1 + l2 * r21) / (1 - r12 * r21); L2 = (l2 + l1 * r12) / (1 - r12 * r21)
    mu1, mu2 = L1 * F(rng.randint(102, 400), 100), L2 * F(rng.randint(102, 400), 100)
    if L2 == 0: continue
    s = jackson(l1, l2, mu1, mu2, r12, r21); res = Q.analyse(s); nj += 1
    exp = {"x_boundary": L1 / mu1, "x_marginal": L1 / mu1, "y_boundary": L2 / mu2, "y_marginal": L2 / mu2}
    for k, (rho, kap) in res.items():
        if abs(rho / Q.M(exp[k]) - 1) > 1e-25 or kap != 0:
            bad += 1; lines.append("Jackson mismatch %s %s" % (k, [str(v) for v in (l1, l2, mu1, mu2, r12, r21)]))
while nf < 120:
    l1, l2, l12 = F(rng.randint(0, 6)), F(rng.randint(0, 6)), F(rng.randint(1, 6))
    m1, m2 = (l1 + l12) * F(rng.randint(102, 300), 100), (l2 + l12) * F(rng.randint(102, 300), 100)
    s = two_demand(l1, l2, l12, m1, m2); res = Q.analyse(s); nf += 1
    for k, e in (("x_marginal", (l1 + l12) / m1), ("y_marginal", (l2 + l12) / m2)):
        rho, kap = res[k]
        if abs(rho / Q.M(e) - 1) > 1e-25 or kap != 0:
            bad += 1; lines.append("Flatto-Hahn mismatch %s %s" % (k, [str(v) for v in (l1, l2, l12, m1, m2)]))
lines.append("Jackson (1957) product form: %d random two-node networks, 4 sequences each" % nj)
lines.append("Flatto-Hahn (1984) M/M/1 marginals: %d random paired-arrival models, 2 marginals each" % nf)
lines.append("mismatches: %d" % bad)
(HERE / "check_literature.txt").write_text("\n".join(lines) + "\n"); print("\n".join(lines))
sys.exit(1 if bad else 0)
