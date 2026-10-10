#!/usr/bin/env python3
"""Exploration aid (not used by solve.sh). Test candidate labellings of nonzero sign vectors for
the zig-zag reduction under the alternation-number hypothesis, on random set systems F with
proper colourings c of KG(F) and t = n - (largest alternation number of a sign vector x with no
member of F inside x^+ or x^-). A labelling works if it is antipodal and has no complementary
pair x <= y with lam(x) = -lam(y)."""
import itertools, random, sys


def signvecs(n):
    for v in itertools.product((-1, 0, 1), repeat=n):
        if any(v):
            yield v


def parts(v):
    return (frozenset(i for i, a in enumerate(v) if a > 0), frozenset(i for i, a in enumerate(v) if a < 0))


def leq(x, y):  # x <= y in the sign-vector order
    return all(a == 0 or a == b for a, b in zip(x, y))


def alt(v):
    nz = [a for a in v if a]
    return 1 + sum(1 for i in range(len(nz) - 1) if nz[i] != nz[i + 1]) if nz else 0


def first_sign(v):
    for a in v:
        if a:
            return a


def alternation_bound(n, F):
    best = 0
    for v in signvecs(n):
        P, N = parts(v)
        if not any(A <= P or A <= N for A in F):
            best = max(best, alt(v))
    return n - best


def make(n, F, c, t, variant):
    s = n - t

    def lam(v):
        P, N = parts(v)
        inside = [A for A in F if A <= P or A <= N]
        if not inside:
            if variant == "cardinality":   # small label ±|x| (sufficient under a defect bound)
                return first_sign(v) * len(P | N)
            return first_sign(v) * alt(v)    # oracle: small label ±alt(x)
        cs = max(c[A] for A in inside)
        pos = any(c[A] == cs and A <= P for A in inside)
        return (1 if pos else -1) * (s + 1 + cs)
    return lam


def check(n, lam):
    V = list(signvecs(n))
    for v in V:
        if lam(tuple(-a for a in v)) != -lam(v):
            return "not antipodal"
    for x in V:
        for y in V:
            if leq(x, y) and lam(x) == -lam(y):
                return f"complementary pair {x} <= {y}"
    return None


random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
variants = ["oracle", "cardinality"]
fails = {v: 0 for v in variants}
trials = 0
for _ in range(200):
    n = random.choice([4, 5])
    subsets = [frozenset(S) for r in (2, 3) for S in itertools.combinations(range(n), r)]
    F = random.sample(subsets, random.randint(3, min(8, len(subsets))))
    c = {}
    for A in random.sample(F, len(F)):
        used = {c[B] for B in c if not (A & B)}
        k = random.randint(0, 2)
        while k in used:
            k += 1
        c[A] = k
    t = alternation_bound(n, F)
    if t <= 0:
        continue
    trials += 1
    for var in variants:
        if check(n, make(n, F, c, t, var)):
            fails[var] += 1
print("instances with t >= 1:", trials)
for v in variants:
    print(f"{v:12s} fails on {fails[v]}")
