#!/usr/bin/env python3
"""Gate-1 baseline: truncate the quarter plane, solve the stationary distribution with a
subtraction-free block GTH elimination, and fit rho and kappa to the computed tails
(local ratio r_n = rho (1 + kappa/n + c/n^2), least squares), kappa rounded to a multiple of 1/2.
usage: b_numeric.py input.json output.json [N]"""
import sys, json
import numpy as np
from fractions import Fraction
sys.path.insert(0, sys.argv[0].rsplit('/', 2)[0])
from gth2d import stationary
N = int(sys.argv[3]) if len(sys.argv) > 3 else 300
def law(d): return {tuple(int(t) for t in k.split(',')): float(Fraction(v)) for k, v in d.items()}
out = {}
for w in json.load(open(sys.argv[1]))['walks']:
    s = {'int': law(w['interior']), 'x': law(w['x_axis']), 'y': law(w['y_axis']), 'o': law(w['origin'])}
    P = stationary(s, N, N)
    seqs = {'x_boundary': P[1:, 0], 'y_boundary': P[0, 1:], 'x_marginal': P.sum(1), 'y_marginal': P.sum(0)}
    res = {}
    for k, v in seqs.items():
        n = np.arange(N // 6, N // 3)
        n = n[(v[n + 1] > 1e-300) & (v[n] > 1e-300)]
        r = v[n + 1] / v[n]
        A = np.vstack([np.ones_like(n, float), 1 / n, 1 / n ** 2]).T
        c = np.linalg.lstsq(A, r, rcond=None)[0]
        kap = Fraction(round(2 * c[1] / c[0]), 2)
        res[k] = {'rho': '%.17g' % c[0], 'kappa': str(kap)}
    out[w['id']] = res
json.dump(out, open(sys.argv[2], 'w'), indent=1)
