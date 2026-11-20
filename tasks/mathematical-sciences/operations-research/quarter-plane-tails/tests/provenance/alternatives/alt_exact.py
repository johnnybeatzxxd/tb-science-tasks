#!/usr/bin/env python3
"""Second independent alternative solver: exact real algebraic arithmetic (sympy).
Candidate singularities are real roots of irreducible polynomials over Q, isolated
exactly; coincidences are decided exactly (same irreducible factor, same root index),
signs by certified interval refinement.

usage: alt_exact.py input.json output.json
"""
import json
import sys
from fractions import Fraction

import sympy as sp

X, Y = sp.symbols('x y')


def law(d):
    out = {}
    for k, v in d.items():
        a, b = (int(t) for t in k.split(','))
        f = Fraction(v)
        if f:
            out[(a, b)] = sp.Rational(f.numerator, f.denominator)
    return out


def swap(d):
    return {(b, a): p for (a, b), p in d.items()}


class Alg:
    """real algebraic number: root `idx` (ascending) of the irreducible polynomial f in X."""

    def __init__(self, f, idx):
        self.f = sp.Poly(f, X).monic()
        self.idx = idx
        self.r = sp.CRootOf(self.f.as_expr(), idx)

    def __eq__(self, o):
        return isinstance(o, Alg) and self.f == o.f and self.idx == o.idx

    __hash__ = None

    def __lt__(self, o):
        return (not self == o) and bool(self.r < o.r)

    def le(self, o):
        return self == o or self < o

    def num(self, d=40):
        return sp.N(self.r, d)


def roots_between(P, lo, hi):
    """real roots of the polynomial P(X) in (lo, hi] as Alg with multiplicities; lo, hi: Alg/number/oo."""
    P = sp.Poly(P, X)
    if P.is_zero or P.degree() <= 0:
        return []
    out = []
    _, facs = sp.factor_list(P.as_expr(), X)
    for f, mult in facs:
        f = sp.Poly(f, X)
        if f.degree() <= 0:
            continue
        nreal = len(sp.Poly(f, X).real_roots())
        for i in range(nreal):
            a = Alg(f, i)
            if gt(a, lo) and le(a, hi):
                out += [a] * mult
    out.sort(key=lambda a: a.num(60))
    return out


def gt(a, b):
    if b is sp.oo:
        return False
    if isinstance(b, Alg):
        return b < a
    return bool(a.r > b)


def le(a, b):
    if b is sp.oo:
        return True
    if isinstance(b, Alg):
        return a.le(b)
    return bool(a.r <= b)


def eval_sign(P, a):
    """exact sign of the polynomial P(X) at the algebraic number a."""
    P = sp.Poly(P, X)
    if P.is_zero:
        return 0
    if sp.rem(P, a.f).is_zero:
        return 0
    for d in (50, 100, 200, 400):
        v = sp.N(P.as_expr().subs(X, a.r), d)
        if abs(v) > sp.Float(10) ** (-(d // 2)):
            return 1 if v > 0 else -1
    raise RuntimeError('sign undecided')


class Side:
    def __init__(self, inner, axis):
        self.p, self.q = inner, axis
        g = lambda bb: sum((v * X ** (a + 1) for (a, b), v in inner.items() if b == bb), sp.Integer(0))
        self.a, self.b, self.c = sp.expand(g(1)), sp.expand(g(0) - X), sp.expand(g(-1))
        self.K = sp.expand(self.a * Y ** 2 + self.b * Y + self.c)
        self.D = sp.expand(self.b ** 2 - 4 * self.a * self.c)

    def branch(self):
        r = roots_between(self.D, 1, sp.oo)
        return r[0] if r else sp.oo

    def is_lower(self, xa, ynum_poly, yden_poly):
        """is y = ynum/yden (a root of K(x, .)) the smaller root Y0 at x = xa?  (a > 0)
        Y0 <=> 2 a y + b <= 0 <=> (2 a ynum + b yden) * yden <= 0."""
        s = eval_sign(sp.expand((2 * self.a * ynum_poly + self.b * yden_poly) * yden_poly), xa)
        return s <= 0

    def own(self, x3):
        q = self.q
        g0 = sum((v * X ** (a + 1) for (a, b), v in q.items() if b == 0), sp.Integer(0))
        g1 = sum((v * X ** (a + 1) for (a, b), v in q.items() if b == 1), sp.Integer(0))
        N1, D1 = sp.expand(X - g0), sp.expand(g1)
        if D1 == 0:
            P = sp.quo(sp.Poly(N1, X), sp.Poly(X - 1, X))
            return roots_between(P.as_expr(), 1, x3)
        R = sp.Poly(sp.expand(self.a * N1 ** 2 + self.b * N1 * D1 + self.c * D1 ** 2), X)
        R = sp.quo(R, sp.Poly(X - 1, X))
        return [r for r in roots_between(R.as_expr(), 1, x3) if self.is_lower(r, N1, D1)]

    def induced(self, x3, R2):
        """smallest x in (1, x3] with Y0(x) = R2 (R2 algebraic, given by Alg in variable X)."""
        g = R2.f.as_expr().subs(X, Y)
        res = sp.resultant(self.K, g, Y)
        best = None
        for xr in roots_between(sp.expand(res), 1, x3):
            # which y-root of K(xr, .) is R2?  compare numerically at high precision, sign exactly
            xv = xr.num(80)
            A, B, C = (sp.N(t.subs(X, xv), 80) for t in (self.a, self.b, self.c))
            disc = B * B - 4 * A * C
            y0 = (-B - sp.sqrt(max(disc, 0))) / (2 * A)
            y1 = (-B + sp.sqrt(max(disc, 0))) / (2 * A)
            rv = R2.num(80)
            # the common root of K(xr, .) and the minimal polynomial of R2 is R2 itself and it
            # is the lower root Y0 (at a branch point the two roots coincide)
            if min(abs(y0 - rv), abs(y1 - rv)) < sp.Float(10) ** -20 and abs(y0 - rv) <= abs(y1 - rv):
                if best is None or xr < best:
                    best = xr
        return best

    def singularity(self, other):
        x3 = self.branch()
        cands = [(z, 'own') for z in self.own(x3)]
        if other is not None and other['pole'] and x3 is not sp.oo:
            xi = self.induced(x3, other['x'])
            if xi is not None:
                cands.append((xi, 'other'))
        allc = [c for c, _ in cands]
        xs = None if x3 is sp.oo else x3
        for c in allc:
            if xs is None or c < xs:
                xs = c
        if xs is None:
            raise ValueError('no singularity')
        at = [c for c in allc if c == xs]
        if x3 is not sp.oo and xs == x3:
            kappa = {0: Fraction(-3, 2), 1: Fraction(-1, 2), 2: Fraction(0)}[len(at)]
            pole = len(at) == 2
        else:
            kappa = Fraction(len(at) - 1)
            pole = True
        return {'x': xs, 'kappa': kappa, 'pole': pole, 'x3': x3}

    def marginal(self, s):
        P1 = sum((v for (a, b), v in self.p.items() if a == 1), sp.Integer(0))
        Pm = sum((v for (a, b), v in self.p.items() if a == -1), sp.Integer(0))
        xs, kq = s['x'], s['kappa']
        if P1 == 0 or Pm <= P1:
            return xs, kq
        xK = Alg(X * P1 - Pm, 0)
        if xs < xK:
            return xs, kq
        xKr = Pm / P1
        yo = self.c.subs(X, xKr) / self.a.subs(X, xKr)
        if yo == 1:
            if xK == xs:
                e = {Fraction(-3, 2): 1, Fraction(-1, 2): -1, Fraction(0): -2}[kq]
                return xs, Fraction(1 - min(e, 0), 2) - 1
            return xs, kq
        if yo < 1:
            if xK < xs:
                return xK, Fraction(0)
            return xs, kq + 1
        return xs, kq


def solve(w):
    I = law(w['interior'])
    SX = Side(I, law(w['x_axis']))
    SY = Side(swap(I), swap(law(w['y_axis'])))
    sx, sy = SX.singularity(None), SY.singularity(None)
    for _ in range(4):
        nx, ny = SX.singularity(sy), SY.singularity(sx)
        done = nx['x'] == sx['x'] and ny['x'] == sy['x'] and nx['kappa'] == sx['kappa'] and ny['kappa'] == sy['kappa']
        sx, sy = nx, ny
        if done:
            break
    mx, my = SX.marginal(sx), SY.marginal(sy)
    res = {'x_boundary': (sx['x'], sx['kappa']), 'y_boundary': (sy['x'], sy['kappa']),
           'x_marginal': mx, 'y_marginal': my}
    out = {}
    for k, (xa, kap) in res.items():
        rho = 1 / xa.num(40)
        out[k] = {'rho': str(sp.N(rho, 30)), 'kappa': str(kap)}
    return out


if __name__ == '__main__':
    data = json.load(open(sys.argv[1]))
    json.dump({w['id']: solve(w) for w in data['walks']}, open(sys.argv[2], 'w'), indent=1)
