#!/usr/bin/env python3
"""Gate-1 positive control: the complete kernel-method classification in IEEE double precision
(numpy.roots, relative coincidence tolerance 1e-8). Shows that the 1e-9 rho tolerance does not
separate correct methods."""
import sys, json
import numpy as np
from fractions import Fraction
TOL = 1e-8
def law(d): return {tuple(int(t) for t in k.split(',')): float(Fraction(v)) for k, v in d.items()}
def tr(L): return {(b, a): p for (a, b), p in L.items()}
def P(c): return np.poly1d(list(reversed(c)))
class Side:
    def __init__(s, I, X):
        s.I, s.X = I, X
        row = lambda bb: [I.get((-1, bb), 0.), I.get((0, bb), 0.), I.get((1, bb), 0.)]
        s.a, b, s.c = P(row(1)), row(0), P(row(-1)); b[1] -= 1; s.b = P(b)
        s.D = s.b * s.b - 4 * s.a * s.c
    def yr(s, x):
        A, B, C = s.a(x), s.b(x), s.c(x); d = max(B * B - 4 * A * C, 0.)
        r = np.sqrt(d); return sorted([(-B - r) / (2 * A), (-B + r) / (2 * A)])
    def real_roots(s, p, lo, hi):
        out = []
        for r in np.roots(p.coeffs) if p.order > 0 else []:
            if abs(r.imag) < 1e-7 * max(1, abs(r)) and lo * (1 + TOL) < r.real <= hi * (1 + TOL): out.append(r.real)
        return sorted(out)
    def x3(s):
        r = s.real_roots(s.D, 1., np.inf); return r[0] if r else np.inf
    def own(s, x3):
        X = s.X
        N1 = P([0., 1.]) - P([X.get((-1, 0), 0.), X.get((0, 0), 0.), X.get((1, 0), 0.)])
        D1 = P([X.get((-1, 1), 0.), X.get((0, 1), 0.), X.get((1, 1), 0.)])
        if not np.any(D1.coeffs):
            q, _ = np.polydiv(N1.coeffs, [1., -1.]); return s.real_roots(np.poly1d(q), 1., x3)
        R = s.a * N1 * N1 + s.b * N1 * D1 + s.c * D1 * D1
        q, _ = np.polydiv(R.coeffs, [1., -1.])
        return [x for x in s.real_roots(np.poly1d(q), 1., x3)
                if abs(N1(x) / D1(x) - s.yr(x)[0]) <= abs(N1(x) / D1(x) - s.yr(x)[1]) + 1e-12]
    def induced(s, x3, R2):
        # K(x, R2) = 0 is quadratic in x
        I = s.I
        A = sum(p * R2 ** (b + 1) for (a, b), p in I.items() if a == 1)
        B = sum(p * R2 ** (b + 1) for (a, b), p in I.items() if a == 0) - R2
        C = sum(p * R2 ** (b + 1) for (a, b), p in I.items() if a == -1)
        best = None
        for x in np.roots([A, B, C]):
            if abs(x.imag) < 1e-9 and 1 + TOL < x.real <= x3 * (1 + TOL):
                y0, y1 = s.yr(x.real)
                if abs(y0 - R2) <= abs(y1 - R2) + 1e-9 * R2:
                    best = x.real if best is None else min(best, x.real)
        return best
    def sing(s, other):
        x3 = s.x3(); c = [(x, 'own') for x in s.own(x3)]
        if other and other[2] and np.isfinite(x3):
            xi = s.induced(x3, other[0])
            if xi is not None: c.append((xi, 'other'))
        xs = min([x3] + [v for v, _ in c]); at = [v for v, _ in c if abs(v - xs) <= TOL * xs]
        if np.isfinite(x3) and abs(xs - x3) <= TOL * xs:
            return (xs, {0: Fraction(-3, 2), 1: Fraction(-1, 2), 2: Fraction(0)}[len(at)], len(at) == 2, x3)
        return (xs, Fraction(len(at) - 1), True, x3)
    def marg(s, sg):
        xs, kq = sg[0], sg[1]
        P1 = sum(p for (a, b), p in s.I.items() if a == 1); Pm = sum(p for (a, b), p in s.I.items() if a == -1)
        if P1 == 0 or Pm <= P1: return xs, kq
        xK = Pm / P1
        if xK > xs * (1 + TOL): return xs, kq
        yo = s.c(xK) / s.a(xK)
        if abs(yo - 1) <= TOL:
            if abs(xK - xs) <= TOL * xs:
                e = {Fraction(-3, 2): 1, Fraction(-1, 2): -1, Fraction(0): -2}[kq]
                return xs, Fraction(1 - min(e, 0), 2) - 1
            return xs, kq
        if yo < 1:
            return (xK, Fraction(0)) if xK < xs * (1 - TOL) else (xs, kq + 1)
        return xs, kq
out = {}
for w in json.load(open(sys.argv[1]))['walks']:
    I = law(w['interior']); SX = Side(I, law(w['x_axis'])); SY = Side(tr(I), tr(law(w['y_axis'])))
    sx, sy = SX.sing(None), SY.sing(None)
    for _ in range(4): sx, sy = SX.sing(sy), SY.sing(sx)
    mx, my = SX.marg(sx), SY.marg(sy)
    res = {'x_boundary': (sx[0], sx[1]), 'y_boundary': (sy[0], sy[1]), 'x_marginal': mx, 'y_marginal': my}
    out[w['id']] = {k: {'rho': '%.17e' % (1 / x), 'kappa': str(kp)} for k, (x, kp) in res.items()}
json.dump(out, open(sys.argv[2], 'w'), indent=1)
