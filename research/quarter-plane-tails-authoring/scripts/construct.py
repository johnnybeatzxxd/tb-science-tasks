"""Exact rational constructions of quarter-plane walks with planted structural events."""
from fractions import Fraction as F
import random
import sympy as sp

INT = [(a, b) for a in (-1, 0, 1) for b in (-1, 0, 1)]
XAX = [(a, b) for a in (-1, 0, 1) for b in (0, 1)]
YAX = [(a, b) for a in (0, 1) for b in (-1, 0, 1)]
ORI = [(a, b) for a in (0, 1) for b in (0, 1)]


def solve_law(keys, eqs, rng, free_scale=None, tries=4000, den=60):
    """Find a probability law on `keys` (nonnegative rationals summing to 1) satisfying the
    linear equations eqs: list of (coef dict, rhs).  Random free entries, solve for len(eqs)+1
    pivot entries.  Returns dict or None."""
    m = len(eqs) + 1
    for _ in range(tries):
        piv = rng.sample(keys, m)
        free = [k for k in keys if k not in piv]
        vals = {}
        for k in free:
            if rng.random() < 0.15:
                vals[k] = F(0)
            else:
                vals[k] = F(rng.randint(1, den), den) * (free_scale or 1)
        # equations: sum p = 1 ; sum coef p = rhs
        A = sp.zeros(m, m); bvec = sp.zeros(m, 1)
        allq = [({k: F(1) for k in keys}, F(1))] + list(eqs)
        for r, (co, rhs) in enumerate(allq):
            s = F(rhs)
            for k in free:
                s -= co.get(k, 0) * vals[k]
            for c, k in enumerate(piv):
                A[r, c] = sp.Rational(co.get(k, 0).numerator, co.get(k, 0).denominator) if isinstance(co.get(k, 0), F) else sp.Rational(co.get(k, 0))
            bvec[r] = sp.Rational(s.numerator, s.denominator)
        if A.det() == 0:
            continue
        sol = A.LUsolve(bvec)
        ok = True
        for c, k in enumerate(piv):
            v = F(int(sp.fraction(sol[c])[0]), int(sp.fraction(sol[c])[1]))
            if v < 0:
                ok = False; break
            vals[k] = v
        if ok:
            return vals
    return None


def coef_phi(keys, x, y):
    """coefficients of phi(x,y) = sum p_ab x^a y^b."""
    return {k: F(x) ** k[0] * F(y) ** k[1] for k in keys}


def coef_Ky(keys, x, y):
    """d/dy [x y (phi - 1)] = sum p (b+1) x^{a+1} y^b - x  ->  coefficient form (rhs x)."""
    return {k: (k[1] + 1) * F(x) ** (k[0] + 1) * F(y) ** k[1] for k in keys}


def rand_law(keys, rng, den=60, zero=0.15):
    while True:
        v = {k: (F(0) if rng.random() < zero else F(rng.randint(1, den))) for k in keys}
        s = sum(v.values())
        if s > 0:
            return {k: x / s for k, x in v.items()}


def interior_with_branch(rng, x3, y3):
    """interior law whose kernel K(x,y)=xy(phi-1) has a double root in y at (x3,y3)."""
    eqs = [(coef_phi(INT, x3, y3), F(1)), (coef_Ky(INT, x3, y3), F(x3))]
    return solve_law(INT, eqs, rng)


def interior_through(rng, x, y):
    return solve_law(INT, [(coef_phi(INT, x, y), F(1))], rng)


def axis_through(keys, rng, x, y):
    return solve_law(keys, [(coef_phi(keys, x, y), F(1))], rng)


def other_x_root(I, x, y):
    """K(.,y) quadratic in x: A x^2 + B x + C with roots x and x'; return x'."""
    A = sum(p * F(y) ** (b + 1) for (a, b), p in I.items() if a == 1)
    C = sum(p * F(y) ** (b + 1) for (a, b), p in I.items() if a == -1)
    return C / (A * F(x)) if A else F(10**9)


def other_y_root(I, x, y):
    A = sum(p * F(x) ** (a + 1) for (a, b), p in I.items() if b == 1)
    C = sum(p * F(x) ** (a + 1) for (a, b), p in I.items() if b == -1)
    return C / (A * F(y)) if A else F(10**9)
