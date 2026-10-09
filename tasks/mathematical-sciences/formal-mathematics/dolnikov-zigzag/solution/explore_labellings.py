#!/usr/bin/env python3
"""Exploration aid (not used by solve.sh). Test candidate labellings of nonzero sign vectors for the zig-zag reduction on random
set systems F with proper colourings c of KG(F). A labelling works if it is antipodal and
has no complementary pair x <= y with lam(x) = -lam(y)."""
import itertools, random, sys

def signvecs(n):
    for v in itertools.product((-1, 0, 1), repeat=n):
        if any(v): yield v

def parts(v):
    return (frozenset(i for i, a in enumerate(v) if a > 0), frozenset(i for i, a in enumerate(v) if a < 0))

def leq(x, y):  # x <= y in the sign-vector order
    return all(a == 0 or a == b for a, b in zip(x, y))

def defect(n, F):
    """largest t with: every D, col with no member of F inside D^c monochromatic has |D| >= t."""
    best = n
    for col in itertools.product((0, 1), repeat=n):
        for r in range(n + 1):
            for D in itertools.combinations(range(n), r):
                Dc = [i for i in range(n) if i not in D]
                if not any(A <= set(Dc) and len({col[i] for i in A}) <= 1 for A in F):
                    best = min(best, r)
    return best

def first_sign(v):
    for a in v:
        if a: return a

def make(n, F, c, t, variant):
    s = n - t
    def lam(v):
        P, N = parts(v)
        inside = [A for A in F if A <= P or A <= N]
        if not inside:
            return first_sign(v) * len(P | N)
        cs = max(c[A] for A in inside)
        pos = any(c[A] == cs and A <= P for A in inside)
        if variant == "oracle":      return (1 if pos else -1) * (s + 1 + cs)
        if variant == "no-offset":   return (1 if pos else -1) * (1 + cs)
        if variant == "first-sign":  return first_sign(v) * (s + 1 + cs)
        if variant == "min-colour":
            cm = min(c[A] for A in inside); posm = any(c[A] == cm and A <= P for A in inside)
            return (1 if posm else -1) * (s + 1 + cm)
    return lam

def check(n, lam):
    V = list(signvecs(n))
    for v in V:
        if lam(tuple(-a for a in v)) != -lam(v): return "not antipodal"
    for x in V:
        for y in V:
            if leq(x, y) and lam(x) == -lam(y): return f"complementary pair {x} <= {y}"
    return None

random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
variants = ["oracle", "no-offset", "first-sign", "min-colour"]
fails = {v: 0 for v in variants}; trials = 0; examples = {}
for _ in range(300):
    n = random.choice([3, 4, 5])
    subsets = [frozenset(S) for r in range(1, n + 1) for S in itertools.combinations(range(n), r)]
    F = random.sample(subsets, random.randint(2, min(8, len(subsets))))
    # greedy proper colouring of KG(F) with shuffled colour order
    c = {}
    for A in random.sample(F, len(F)):
        used = {c[B] for B in c if not (A & B)}
        k = 0
        while k in used: k += 1
        c[A] = k + random.randint(0, 2)
        while c[A] in used: c[A] += 1
    t = defect(n, F)
    if t == 0: continue
    trials += 1
    for var in variants:
        r = check(n, make(n, F, c, t, var))
        if r:
            fails[var] += 1
            examples.setdefault(var, (n, sorted(map(sorted, F)), {tuple(sorted(A)): c[A] for A in F}, t, r))
print("instances with t >= 1:", trials)
for v in variants: print(f"{v:12s} fails on {fails[v]}")
for v, e in examples.items(): print(v, "example:", e)
