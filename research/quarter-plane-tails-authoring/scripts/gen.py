"""Generators of walks with planted structural events (exact rational constructions)."""
import random
from fractions import Fraction as F
from construct import solve_law, coef_phi, coef_Ky, rand_law, INT, XAX, YAX, ORI, other_x_root
from val import ergodic, nondeg

def dphi(keys, x, y, var):
    """coefficients of d phi/dx (var=0) or d phi/dy (var=1) at (x,y)."""
    out = {}
    for k in keys:
        a, b = k
        if var == 0:
            out[k] = a * F(x) ** (a - 1) * F(y) ** b if a else F(0)
        else:
            out[k] = b * F(x) ** a * F(y) ** (b - 1) if b else F(0)
    return out


def phi_val(law, x, y):
    return sum(p * F(x) ** a * F(y) ** b for (a, b), p in law.items())


def dphi_val(law, x, y, var):
    co = dphi(list(law), x, y, var)
    return sum(co[k] * law[k] for k in law)


def rnum(rng, lo, hi, den):
    return F(rng.randint(int(lo * den), int(hi * den)), den)


def finish(I, X, Y, O):
    s = {'int': I, 'x': X, 'y': Y, 'o': O}
    for d in s.values():
        for k in list(d):
            if d[k] == 0:
                del d[k]
    return s


def make(kind, rng, lo=1.05, hi=3.0, den=20, axis_den=60, ylo=0.5, yhi=None):
    yhi = hi if yhi is None else yhi
    """returns a walk spec with a planted event on the x-side (or None)."""
    O = rand_law(ORI, rng, zero=0.1)
    if kind == 'own_branch':
        x3, y3 = rnum(rng, lo, hi, den), rnum(rng, ylo, yhi, den)
        I = solve_law(INT, [(coef_phi(INT, x3, y3), F(1)), (coef_Ky(INT, x3, y3), F(x3))], rng, tries=300)
        if I is None: return None
        X = solve_law(XAX, [(coef_phi(XAX, x3, y3), F(1))], rng, den=axis_den)
        Y = rand_law(YAX, rng)
    elif kind == 'other_branch':
        x3, y3 = rnum(rng, lo, hi, den), rnum(rng, lo, hi, den)
        I = solve_law(INT, [(coef_phi(INT, x3, y3), F(1)), (coef_Ky(INT, x3, y3), F(x3))], rng)
        if I is None: return None
        xo = other_x_root(I, x3, y3)
        if not (0 < xo < x3): return None
        Y = solve_law(YAX, [(coef_phi(YAX, xo, y3), F(1))], rng, den=axis_den)
        X = rand_law(XAX, rng)
    elif kind == 'both_branch':
        x3, y3 = rnum(rng, lo, hi, den), rnum(rng, lo, hi, den)
        I = solve_law(INT, [(coef_phi(INT, x3, y3), F(1)), (coef_Ky(INT, x3, y3), F(x3))], rng)
        if I is None: return None
        xo = other_x_root(I, x3, y3)
        if not (0 < xo < x3): return None
        Y = solve_law(YAX, [(coef_phi(YAX, xo, y3), F(1))], rng, den=axis_den)
        X = solve_law(XAX, [(coef_phi(XAX, x3, y3), F(1))], rng, den=axis_den)
    elif kind == 'double_pole':
        xs, ys = rnum(rng, lo, hi, den), rnum(rng, max(lo, ylo), yhi, den)
        I = solve_law(INT, [(coef_phi(INT, xs, ys), F(1))], rng, tries=300)
        if I is None: return None
        xo = other_x_root(I, xs, ys)
        if not (0 < xo < xs): return None
        X = solve_law(XAX, [(coef_phi(XAX, xs, ys), F(1))], rng, den=axis_den)
        Y = solve_law(YAX, [(coef_phi(YAX, xo, ys), F(1))], rng, den=axis_den)
    elif kind == 'tangent':
        xs, ys = rnum(rng, lo, hi, den), rnum(rng, 0.5, hi, den)
        I = solve_law(INT, [(coef_phi(INT, xs, ys), F(1))], rng)
        if I is None: return None
        gx, gy = dphi_val(I, xs, ys, 0), dphi_val(I, xs, ys, 1)
        cx, cy = dphi(XAX, xs, ys, 0), dphi(XAX, xs, ys, 1)
        tang = {k: cx[k] * gy - cy[k] * gx for k in XAX}
        X = solve_law(XAX, [(coef_phi(XAX, xs, ys), F(1)), (tang, F(0))], rng, den=axis_den)
        Y = rand_law(YAX, rng)
    elif kind == 'marg_double':
        # interior pole x_K coincides with the own boundary pole, (x_K,1) on the upper branch
        I = rand_law(INT, rng)
        P1 = sum(v for (a, b), v in I.items() if a == 1); Pm = sum(v for (a, b), v in I.items() if a == -1)
        if P1 == 0 or Pm <= P1: return None
        xK = Pm / P1
        A = sum(v * xK ** (a + 1) for (a, b), v in I.items() if b == 1)
        C = sum(v * xK ** (a + 1) for (a, b), v in I.items() if b == -1)
        yo = C / A
        if not yo < 1: return None
        X = solve_law(XAX, [(coef_phi(XAX, xK, yo), F(1))], rng, den=axis_den)
        Y = rand_law(YAX, rng)
    elif kind == 'marg_branch':
        x3 = rnum(rng, lo, hi, den)
        I = solve_law(INT, [(coef_phi(INT, x3, 1), F(1)), (coef_Ky(INT, x3, 1), F(x3))], rng)
        if I is None: return None
        X = rand_law(XAX, rng); Y = rand_law(YAX, rng)
    elif kind == 'random':
        I, X, Y = rand_law(INT, rng), rand_law(XAX, rng), rand_law(YAX, rng)
    else:
        raise ValueError(kind)
    if X is None or Y is None:
        return None
    s = finish(I, X, Y, O)
    if not (ergodic(s) and nondeg(s)):
        return None
    if s['int'].get((0, 0), 0) == 0 and s['x'].get((0, 0), 0) == 0 and s['y'].get((0, 0), 0) == 0:
        return None
    return s
