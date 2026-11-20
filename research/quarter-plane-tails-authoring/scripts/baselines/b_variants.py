#!/usr/bin/env python3
"""Partial-knowledge variants of the kernel-method solution (gate-1 baselines).
usage: b_variants.py VARIANT input.json output.json
  generic   : own boundary poles and branch point only; marginal = min(interior pole, boundary)
  noinduced : full boundary theory except the pole induced from the other axis
  nocancel  : full boundary theory; marginal interior pole never cancelled
  nocoinc   : full theory, but coincident singularities are not merged (kappa from the smallest only)
  float     : full theory at 16 significant digits with a 1e-9 relative coincidence tolerance
"""
import sys, json
from fractions import Fraction
sys.path.insert(0, sys.argv[0].rsplit('/', 2)[0])
import qtails as Q
import mpmath as mp
V = sys.argv[1]
if V in ('generic', 'noinduced'):
    Q.induced_point = lambda s, x3, R2: None
if V in ('generic', 'nocancel'):
    orig = Q.marginal
    def marginal(s, bx):
        p = s['int']
        P1 = sum(v for (a, b), v in p.items() if a == 1); Pm = sum(v for (a, b), v in p.items() if a == -1)
        if P1 == 0 or Pm <= P1: return bx['x'], bx['kappa']
        xK = Q.M(Pm / P1)
        if xK < bx['x'] * (1 - Q.TIGHT): return xK, Fraction(0)
        if abs(xK - bx['x']) < Q.TIGHT * bx['x']: return bx['x'], bx['kappa'] + 1
        return bx['x'], bx['kappa']
    Q.marginal = marginal
if V == 'float':
    # the complete theory in double-precision-like arithmetic with a relative coincidence tolerance
    mp.mp.dps = 16
    Q.TIGHT = mp.mpf('1e-9'); Q.ROOT_IM = mp.mpf('1e-7')
if V == 'nocoinc':
    Q.TIGHT = mp.mpf(0)
data = json.load(open(sys.argv[2]))
json.dump({w['id']: Q.fmt(Q.analyse(Q.parse_walk(w))) for w in data['walks']}, open(sys.argv[3], 'w'), indent=1)
