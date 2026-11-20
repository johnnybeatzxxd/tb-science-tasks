#!/usr/bin/env python3
"""Independent alternative solver: convex geometry of the level curves in log
coordinates theta = (log x, log y) (Miyazawa-style), solved with bracketing and
Newton iterations on exponential sums -- no polynomial root finding.

usage: alt_theta.py input.json output.json
"""
import json
import sys
from fractions import Fraction

import mpmath as mp

mp.mp.dps = 60
EPS = mp.mpf(10) ** -28


def law(d):
    out = {}
    for k, v in d.items():
        a, b = (int(t) for t in k.split(','))
        f = Fraction(v)
        if f:
            out[(a, b)] = mp.mpf(f.numerator) / f.denominator
    return out


def swap(d):
    return {(b, a): p for (a, b), p in d.items()}


class Side:
    """everything needed for the boundary on the theta1 axis (L2 = 0)."""

    def __init__(self, inner, axis):
        self.p = inner
        self.q = axis

    # gamma(t1, t2) = sum p e^{a t1 + b t2} - 1, written as A e^{t2} + B + C e^{-t2} - 1
    def abc(self, t1):
        A = B = C = mp.mpf(0)
        for (a, b), v in self.p.items():
            w = v * mp.e ** (a * t1)
            if b == 1:
                A += w
            elif b == 0:
                B += w
            else:
                C += w
        return A, B, C

    def gmin(self, t1):
        A, B, C = self.abc(t1)
        return B - 1 + 2 * mp.sqrt(A * C)

    def rightmost(self):
        """largest t1 > 0 with min_t2 gamma(t1, t2) = 0 (inf if the curve is unbounded)."""
        lo = mp.mpf(0)
        hi = mp.mpf('0.5')
        while self.gmin(hi) < 0:
            lo = hi
            hi *= 2
            if hi > 200:
                return mp.inf
        # gmin(lo) <= 0 < gmin(hi); gmin is convex
        for _ in range(400):
            mid = (lo + hi) / 2
            if self.gmin(mid) <= 0:
                lo = mid
            else:
                hi = mid
            if hi - lo < mp.mpf(10) ** -55:
                break
        return (lo + hi) / 2

    def t2_low_high(self, t1):
        A, B, C = self.abc(t1)
        disc = (1 - B) ** 2 - 4 * A * C
        if disc < 0:
            disc = mp.mpf(0)
        r = mp.sqrt(disc)
        y0 = (1 - B - r) / (2 * A)
        y1 = (1 - B + r) / (2 * A)
        return mp.log(y0), mp.log(y1)

    def gamma1(self, t1, t2):
        return sum(v * mp.e ** (a * t1 + b * t2) for (a, b), v in self.q.items()) - 1

    def roots_on_low_arc(self, f, tR, ngrid=4000):
        """roots of f(t1) on (0, tR] (sign changes, tangencies and the endpoint)."""
        pts = [tR * k / ngrid for k in range(1, ngrid + 1)]
        vals = [f(t) for t in pts]
        roots = []
        # sign changes
        for k in range(len(pts) - 1):
            if vals[k] == 0:
                roots.append((pts[k], 1))
            elif vals[k] * vals[k + 1] < 0:
                roots.append((mp.findroot(f, (pts[k], pts[k + 1]), solver='anderson'), 1))
        if abs(vals[-1]) < EPS:
            roots.append((tR, 1))
        # tangencies: local minima of |f| without a sign change
        for k in range(1, len(pts) - 1):
            if abs(vals[k]) < abs(vals[k - 1]) and abs(vals[k]) < abs(vals[k + 1]) and \
                    vals[k - 1] * vals[k + 1] > 0 and vals[k] * vals[k - 1] > 0:
                try:
                    d = lambda t: mp.diff(f, t)
                    tc = mp.findroot(d, (pts[k - 1], pts[k + 1]), solver='anderson')
                    if abs(f(tc)) < EPS:
                        roots.append((tc, 2))
                except Exception:
                    pass
        # refine and merge
        out = []
        for t, m in sorted(roots, key=lambda r: r[0]):
            if t <= mp.mpf(10) ** -20:
                continue
            if out and abs(out[-1][0] - t) < mp.mpf(10) ** -20:
                continue
            out.append((t, m))
        return out

    def singularity(self, other):
        tR = self.rightmost()
        if tR == mp.inf:
            raise ValueError('unbounded level curve')
        f = lambda t: self.gamma1(t, self.t2_low_high(t)[0])
        cands = []
        for t, m in self.roots_on_low_arc(f, tR):
            cands += [t] * m
        if other is not None and other[1]:
            lr = mp.log(other[0])
            g = lambda t: self.t2_low_high(t)[0] - lr
            hits = [t for t, m in self.roots_on_low_arc(g, tR)]
            if hits:
                cands.append(hits[0])
        ts = min([tR] + cands)
        at = [c for c in cands if abs(c - ts) < mp.mpf(10) ** -20]
        if abs(ts - tR) < mp.mpf(10) ** -20:
            kappa = {0: Fraction(-3, 2), 1: Fraction(-1, 2), 2: Fraction(0)}[len(at)]
            pole = len(at) == 2
        else:
            kappa = Fraction(len(at) - 1)
            pole = True
        return {'x': mp.e ** ts, 'kappa': kappa, 'pole': pole, 'tR': tR}

    def marginal(self, sing):
        P1 = sum(v for (a, b), v in self.p.items() if a == 1)
        Pm = sum(v for (a, b), v in self.p.items() if a == -1)
        xs, kq = sing['x'], sing['kappa']
        if P1 == 0 or Pm <= P1:
            return xs, kq
        tK = mp.log(Pm / P1)               # gamma(tK, 0) = 0
        if mp.e ** tK > xs * (1 + mp.mpf(10) ** -20):
            return xs, kq
        lo, hi = self.t2_low_high(tK)
        if abs(lo) < mp.mpf(10) ** -20 and abs(hi) < mp.mpf(10) ** -20:
            return (xs, Fraction(-1, 2)) if abs(tK - sing['tR']) < mp.mpf(10) ** -20 else (xs, kq)
        if abs(hi) < mp.mpf(10) ** -20:      # (tK, 0) on the upper arc: genuine pole
            if mp.e ** tK < xs * (1 - mp.mpf(10) ** -20):
                return mp.e ** tK, Fraction(0)
            return xs, kq + 1
        return xs, kq                        # on the lower arc: cancelled


def solve(w):
    I = law(w['interior'])
    X = Side(I, law(w['x_axis']))
    Y = Side(swap(I), swap(law(w['y_axis'])))
    sx, sy = X.singularity(None), Y.singularity(None)
    for _ in range(4):
        nx = X.singularity((sy['x'], sy['pole']))
        ny = Y.singularity((sx['x'], sx['pole']))
        done = abs(nx['x'] - sx['x']) < EPS and abs(ny['x'] - sy['x']) < EPS
        sx, sy = nx, ny
        if done:
            break
    mx, my = X.marginal(sx), Y.marginal(sy)
    res = {'x_boundary': (1 / sx['x'], sx['kappa']), 'y_boundary': (1 / sy['x'], sy['kappa']),
           'x_marginal': (1 / mx[0], mx[1]), 'y_marginal': (1 / my[0], my[1])}
    return {k: {'rho': mp.nstr(r, 25), 'kappa': str(kap)} for k, (r, kap) in res.items()}


if __name__ == '__main__':
    data = json.load(open(sys.argv[1]))
    json.dump({w['id']: solve(w) for w in data['walks']}, open(sys.argv[2], 'w'), indent=1)
