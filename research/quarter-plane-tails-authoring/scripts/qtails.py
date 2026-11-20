#!/usr/bin/env python3
"""Reference solver: exact tail asymptotics of the stationary distribution of a
two-dimensional reflected nearest-neighbour random walk on the quarter plane
(kernel method: analytic continuation of the boundary generating functions along
the real branch of the kernel curve).

usage: qtails.py input.json output.json
"""
import json
import sys
from fractions import Fraction

import mpmath as mp

mp.mp.dps = 80
TIGHT = mp.mpf(10) ** -30     # coincidence of two algebraic candidates
ROOT_IM = mp.mpf(10) ** -35   # imaginary part of a real root

INT = [(a, b) for a in (-1, 0, 1) for b in (-1, 0, 1)]


# ----------------------------------------------------------------- input --
def parse_law(d):
    law = {}
    for k, v in d.items():
        a, b = (int(t) for t in k.split(','))
        law[(a, b)] = Fraction(v)
    return law


def parse_walk(w):
    return {'int': parse_law(w['interior']), 'x': parse_law(w['x_axis']),
            'y': parse_law(w['y_axis']), 'o': parse_law(w['origin'])}


def transpose(s):
    sw = lambda d: {(b, a): p for (a, b), p in d.items()}
    return {'int': sw(s['int']), 'x': sw(s['y']), 'y': sw(s['x']), 'o': sw(s['o'])}


def M(q):
    return mp.mpf(q.numerator) / q.denominator


# ----------------------------------------------------------- polynomials --
def padd(a, b):
    n = max(len(a), len(b))
    return [(a[k] if k < len(a) else 0) + (b[k] if k < len(b) else 0) for k in range(n)]


def pmul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            r[i + j] += x * y
    return r


def ptrim(a):
    a = list(a)
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


def pev(a, x):
    r = 0
    for c in reversed(a):
        r = r * x + c
    return r


def deflate_one(p):
    """exact division of an exact (Fraction) polynomial by (x-1); requires p(1)=0."""
    p = ptrim(p)
    assert sum(p) == 0
    q = [Fraction(0)] * (len(p) - 1)
    acc = Fraction(0)
    for k in range(len(p) - 1, 0, -1):
        acc += p[k]
        q[k - 1] = acc
    return q


def real_roots(p, lo, hi):
    """real roots (with multiplicity) of an exact polynomial in the open-closed interval (lo, hi]."""
    p = ptrim(p)
    if len(p) <= 1:
        return []
    rts = mp.polyroots([M(c) for c in reversed(p)], maxsteps=2000, extraprec=600)
    out = []
    for r in rts:
        r = mp.mpc(r)
        if abs(r.imag) < ROOT_IM * max(1, abs(r)) and lo + TIGHT < r.real <= hi + TIGHT:
            out.append(r.real)
    return sorted(out)


# --------------------------------------------------------------- kernel --
def kernel_abc(s):
    """K(x,y) = x y (phi(x,y) - 1) = a(x) y^2 + b(x) y + c(x), coefficients exact."""
    p = s['int']
    row = lambda bb: [p.get((-1, bb), Fraction(0)), p.get((0, bb), Fraction(0)), p.get((1, bb), Fraction(0))]
    a, b, c = row(1), row(0), row(-1)
    b[1] -= 1
    return a, b, c


def discriminant(s):
    a, b, c = kernel_abc(s)
    return padd(pmul(b, b), [-4 * t for t in pmul(a, c)])


def y_roots(s, x):
    """the two real roots Y0 <= Y1 of K(x, .) = 0 at a real point x of the cut-free interval."""
    a, b, c = kernel_abc(s)
    A, B, C = pev([M(t) for t in a], x), pev([M(t) for t in b], x), pev([M(t) for t in c], x)
    D = B * B - 4 * A * C
    if D < 0:
        D = mp.mpf(0)
    r = mp.sqrt(D)
    y0, y1 = (-B - r) / (2 * A), (-B + r) / (2 * A)
    return (y0, y1) if y0 <= y1 else (y1, y0)


def x_roots_at(s, y):
    """real roots of K(., y) = 0 (quadratic in x)."""
    return y_roots(transpose(s), y)


def branch_point(s):
    """x3: the first zero of the discriminant to the right of 1 (end of the real cut-free
    interval of Y0); mp.inf if there is none."""
    rts = real_roots(discriminant(s), mp.mpf(1), mp.inf)
    return rts[0] if rts else mp.inf


def own_zeros(s, x3):
    """zeros in (1, x3] of K1(x, Y0(x)) with multiplicity, where K1 = x y (phi1 - 1)."""
    q = s['x']
    g0 = [q.get((-1, 0), Fraction(0)), q.get((0, 0), Fraction(0)), q.get((1, 0), Fraction(0))]
    g1 = [q.get((-1, 1), Fraction(0)), q.get((0, 1), Fraction(0)), q.get((1, 1), Fraction(0))]
    N1 = padd([Fraction(0), Fraction(1)], [-t for t in g0])     # x (1 - phi1^(0))
    D1 = g1                                                      # x phi1^(1)
    if all(t == 0 for t in D1):
        # K1 does not depend on y: zeros are the zeros of N1
        return [(x, 'N') for x in real_roots(deflate_one(N1), mp.mpf(1), x3)]
    a, b, c = kernel_abc(s)
    poly = padd(padd(pmul(a, pmul(N1, N1)), pmul(b, pmul(N1, D1))), pmul(c, pmul(D1, D1)))
    poly = deflate_one(poly)      # (1,1) lies on both curves
    out = []
    for x in real_roots(poly, mp.mpf(1), x3):
        y = pev([M(t) for t in N1], x) / pev([M(t) for t in D1], x)
        y0, y1 = y_roots(s, x)
        if abs(y - y0) < mp.mpf(10) ** -30 * max(1, abs(y0)):
            out.append((x, 'Y0'))
    return out


def induced_point(s, x3, R2):
    """smallest x in (1, x3] with Y0(x) = R2 (R2 a pole of the other boundary function)."""
    best = None
    for x in x_roots_at(s, R2):
        if 1 + TIGHT < x <= x3 + TIGHT:
            y0, _ = y_roots(s, x)
            if abs(y0 - R2) < mp.mpf(10) ** -30 * R2:
                best = x if best is None else min(best, x)
    return best


def boundary_singularity(s, other):
    """first singularity of the x-axis boundary generating function.
    other: (R, is_pole) of the y-axis boundary function or None.
    returns dict(x=..., kappa=..., poles=[...], x3=...)."""
    x3 = branch_point(s)
    cands = [(x, 'own') for x, _ in own_zeros(s, x3)]
    if other is not None and other[1] and x3 != mp.inf:
        xi = induced_point(s, x3, other[0])
        if xi is not None:
            cands.append((xi, 'other'))
    xs = min([x3] + [c[0] for c in cands])
    at = [c for c in cands if abs(c[0] - xs) < TIGHT * xs]
    if x3 != mp.inf and abs(xs - x3) < TIGHT * xs:
        o = len(at)
        kappa = {0: Fraction(-3, 2), 1: Fraction(-1, 2), 2: Fraction(0)}[o]
        is_pole = (o == 2)
    else:
        kappa = Fraction(len(at) - 1)
        is_pole = True
    return {'x': xs, 'kappa': kappa, 'is_pole': is_pole, 'x3': x3, 'sources': [c[1] for c in at]}


def boundaries(s):
    t = transpose(s)
    bx = boundary_singularity(s, None)
    by = boundary_singularity(t, None)
    for _ in range(4):
        nbx = boundary_singularity(s, (by['x'], by['is_pole']))
        nby = boundary_singularity(t, (bx['x'], bx['is_pole']))
        same = (abs(nbx['x'] - bx['x']) < TIGHT and abs(nby['x'] - by['x']) < TIGHT
                and nbx['kappa'] == bx['kappa'] and nby['kappa'] == by['kappa'])
        bx, by = nbx, nby
        if same:
            break
    return bx, by


def marginal(s, bx):
    """first singularity of the generating function of P(L1 = n)."""
    p = s['int']
    P1 = sum((v for (a, b), v in p.items() if a == 1), Fraction(0))
    Pm = sum((v for (a, b), v in p.items() if a == -1), Fraction(0))
    xs, kq = bx['x'], bx['kappa']
    if P1 == 0 or Pm <= P1:
        return xs, kq                       # x_K <= 1 or infinite: no interior pole
    xK = Pm / P1                            # exact rational
    # other root of K(xK, .) = 0 besides y = 1
    a, b, c = kernel_abc(s)
    A, C = pev(a, xK), pev(c, xK)
    yo = C / A                              # exact rational: roots are 1 and yo
    xKm = M(xK)
    if xKm > xs + TIGHT * xs:
        return xs, kq                       # beyond the boundary singularity
    if yo == 1:
        # (xK, 1) is the rightmost point of the kernel curve (xK = x3).  With s = sqrt(x3 - x),
        # the boundary function behaves like s^e (e = 1, -1, -2 for kappa = -3/2, -1/2, 0); the
        # numerator of Q(x,1) is O(s^(1+min(e,0))) and K(x,1) = O(s^2), so the marginal behaves
        # like s^(-1+min(e,0)).
        if abs(xKm - xs) < TIGHT * xs:
            e = -2 * (kq + 1)
            f = -1 + min(e, 0)
            return xs, Fraction(-f, 2) - 1
        return xs, kq
    if yo < 1:
        # (xK, 1) on the upper branch: genuine pole of the marginal
        if xKm < xs - TIGHT * xs:
            return xKm, Fraction(0)
        # coincides with a pole of the boundary function
        return xs, kq + 1
    # (xK, 1) on the lower branch: the kernel identity cancels the pole
    return xs, kq


def analyse(s):
    bx, by = boundaries(s)
    t = transpose(s)
    mx = marginal(s, bx)
    my = marginal(t, by)
    return {'x_boundary': (1 / bx['x'], bx['kappa']), 'y_boundary': (1 / by['x'], by['kappa']),
            'x_marginal': (1 / mx[0], mx[1]), 'y_marginal': (1 / my[0], my[1])}


def fmt(res):
    return {k: {'rho': mp.nstr(r, 30, strip_zeros=False), 'kappa': str(kap)} for k, (r, kap) in res.items()}


def main():
    inp, outp = sys.argv[1], sys.argv[2]
    data = json.load(open(inp))
    out = {}
    for w in data['walks']:
        out[w['id']] = fmt(analyse(parse_walk(w)))
    json.dump(out, open(outp, 'w'), indent=1)


if __name__ == '__main__':
    main()
