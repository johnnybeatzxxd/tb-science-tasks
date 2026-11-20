"""Independent numerical check of the held-out answers: subtraction-free block-GTH solution of a
large truncation, local exponent kappa_n = n (a_{n+1}/(rho a_n) - 1) with the reference rho."""
import sys, json, pickle
import numpy as np
from fractions import Fraction as F
from gth2d import stationary
sets = pickle.load(open('sets.pkl', 'rb'))
exp = json.load(open(sys.argv[1]))
Nmax = int(sys.argv[2])
only = sys.argv[3].split(',') if len(sys.argv) > 3 else None
for name, s, wid in sets['held']:
    if only and wid not in only: continue
    rhos = {k: float(F(v['rho'])) for k, v in exp[wid].items()}
    worst = max(rhos.values())
    N = min(Nmax, max(200, int(12 / (1 - worst))))
    sf = {k: {kk: float(vv) for kk, vv in d.items()} for k, d in s.items()}
    P = stationary(sf, N, N)
    seq = {'x_boundary': P[1:, 0], 'y_boundary': P[0, 1:], 'x_marginal': P.sum(1), 'y_marginal': P.sum(0)}
    for k, v in seq.items():
        rho = rhos[k]; kap = exp[wid][k]['kappa']
        ns = [m for m in (N // 10, N // 6, N // 4, N // 3) if v[m + 1] > 1e-280]
        kn = [m * (v[m + 1] / v[m] / rho - 1) for m in ns]
        print('%s %-34s %-10s rho %.6f kappa %5s | N=%d kappa_n %s' % (wid, name[:34], k, rho, kap, N,
              ' '.join('%d:%+.3f' % (m, z) for m, z in zip(ns, kn))), flush=True)
