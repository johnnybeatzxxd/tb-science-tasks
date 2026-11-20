"""Quarter-plane walks from classical two-queue models (uniformised CTMCs), exact rationals.
Every model returns spec dict {'int','x','y','o'} of laws {(a,b): Fraction}."""
from fractions import Fraction as F


def uniformise(rates_by_region, U):
    """rates_by_region: dict region -> {(a,b): rate}; U uniformisation constant (> max total)."""
    spec = {}
    for reg, rates in rates_by_region.items():
        law = {}
        tot = F(0)
        for k, r in rates.items():
            r = F(r)
            if r:
                law[k] = law.get(k, F(0)) + r / U
                tot += r
        assert tot < U, (reg, tot, U)
        law[(0, 0)] = law.get((0, 0), F(0)) + 1 - tot / U
        spec[reg] = law
    return spec


def tandem(lam, mu1, mu2, U=None):
    lam, mu1, mu2 = F(lam), F(mu1), F(mu2)
    U = U or (lam + mu1 + mu2) * F(11, 10)
    return uniformise({
        'int': {(1, 0): lam, (-1, 1): mu1, (0, -1): mu2},
        'x': {(1, 0): lam, (-1, 1): mu1},
        'y': {(1, 0): lam, (0, -1): mu2},
        'o': {(1, 0): lam}}, U)


def jackson(l1, l2, mu1, mu2, r12, r21, U=None):
    """two-node Jackson network: external arrivals l_i, service mu_i, routing r12 (1->2), r21 (2->1)."""
    l1, l2, mu1, mu2, r12, r21 = map(F, (l1, l2, mu1, mu2, r12, r21))
    U = U or (l1 + l2 + mu1 + mu2) * F(11, 10)
    i = {(1, 0): l1, (0, 1): l2, (-1, 0): mu1 * (1 - r12), (-1, 1): mu1 * r12,
         (0, -1): mu2 * (1 - r21), (1, -1): mu2 * r21}
    return uniformise({
        'int': i,
        'x': {k: v for k, v in i.items() if k[1] >= 0},
        'y': {k: v for k, v in i.items() if k[0] >= 0},
        'o': {(1, 0): l1, (0, 1): l2}}, U)


def coupled_processors(l1, l2, mu1, mu2, mu1s, mu2s, U=None):
    """Fayolle-Iasnogorodski: service rates mu_i when both busy, mu_i* when the other queue is empty."""
    l1, l2, mu1, mu2, mu1s, mu2s = map(F, (l1, l2, mu1, mu2, mu1s, mu2s))
    U = U or (l1 + l2 + max(mu1 + mu2, mu1s, mu2s)) * F(11, 10)
    return uniformise({
        'int': {(1, 0): l1, (0, 1): l2, (-1, 0): mu1, (0, -1): mu2},
        'x': {(1, 0): l1, (0, 1): l2, (-1, 0): mu1s},
        'y': {(1, 0): l1, (0, 1): l2, (0, -1): mu2s},
        'o': {(1, 0): l1, (0, 1): l2}}, U)


def two_demand(l1, l2, l12, mu1, mu2, U=None, help1=0, help2=0):
    """parallel queues with single and paired arrivals (Flatto-Hahn / Wright); optional extra
    service rate help_i given to queue i when the other queue is empty."""
    l1, l2, l12, mu1, mu2, help1, help2 = map(F, (l1, l2, l12, mu1, mu2, help1, help2))
    U = U or (l1 + l2 + l12 + mu1 + mu2 + help1 + help2) * F(11, 10)
    a = {(1, 0): l1, (0, 1): l2, (1, 1): l12}
    return uniformise({
        'int': {**a, (-1, 0): mu1, (0, -1): mu2},
        'x': {**a, (-1, 0): mu1 + help1},
        'y': {**a, (0, -1): mu2 + help2},
        'o': dict(a)}, U)
