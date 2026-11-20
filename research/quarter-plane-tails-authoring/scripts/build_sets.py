"""Assemble the public examples and the held-out set; compute reference answers with the
reference solver, cross-check every answer with the independent theta-space solver, and
write the task files plus an authoring provenance table."""
import json, pickle, random, sys
from fractions import Fraction as F
from models import tandem, jackson, coupled_processors, two_demand
from cpplant import cp_own_at_branch
from gen import make
from val import ergodic, nondeg
from wio import walk_json
import qtails as Q, alt_theta as A, alt_exact as E

TASK = sys.argv[1] if len(sys.argv) > 1 else "."


def jackson_rho(l1, l2, r12, r21, rho1, rho2):
    l1, l2, r12, r21 = map(F, (l1, l2, r12, r21))
    L1 = (l1 + l2 * r21) / (1 - r12 * r21); L2 = (l2 + l1 * r12) / (1 - r12 * r21)
    return jackson(l1, l2, L1 / F(rho1), L2 / F(rho2), r12, r21)


def planted(kind, seed, want_key, want, lo=1.05, hi=3.0, extra=None, den=20, ylo=0.5, yhi=None):
    rng = random.Random(seed)
    for _ in range(20000):
        s = make(kind, rng, lo=lo, hi=hi, den=den, ylo=ylo, yhi=yhi)
        if s is None:
            continue
        r = Q.analyse(s)
        if str(r[want_key][1]) != want or min(float(v[0]) for v in r.values()) < 0.05:
            continue
        if extra and not extra(r):
            continue
        if Q.branch_point(s) == Q.mp.inf or Q.branch_point(Q.transpose(s)) == Q.mp.inf:
            continue
        try:
            A.solve(walk_json(s, 'chk'))
        except Exception:
            continue
        return s
    raise RuntimeError(kind)


def rand_generic(seed, pred):
    rng = random.Random(seed)
    from val import randwalk
    for _ in range(5000):
        s = randwalk(rng)
        r = Q.analyse(s)
        if min(float(v[0]) for v in r.values()) < 0.05:
            continue
        if pred(s, r):
            return s
    raise RuntimeError('generic')


def drift(d):
    return (sum(a * p for (a, b), p in d.items()), sum(b * p for (a, b), p in d.items()))


EXAMPLES = [
    ('jackson', jackson_rho(2, 1, F(1, 3), F(1, 4), F(1, 2), F(2, 3))),
    ('coupled processors', coupled_processors(1, 1, 2, F(3, 2), 3, F(5, 2))),
    ('two-demand', two_demand(1, 2, 1, 5, 6)),
    ('random', rand_generic(101, lambda s, r: str(r['x_boundary'][1]) == '-3/2' and str(r['y_boundary'][1]) == '0')),
]

HELD = [
    ('jackson feedback', jackson_rho(3, 2, F(1, 2), F(1, 4), F(3, 5), F(7, 10))),
    ('jackson heavy traffic', jackson_rho(2, 1, F(1, 3), F(1, 5), F(49, 50), F(24, 25))),
    ('tandem', tandem(1, F(9, 4), F(3, 2))),
    ('tandem heavy traffic', tandem(1, F(50, 49), F(25, 24))),
    ('coupled processors near-miss', coupled_processors(2, 3, 6, 9, 11, 4)),
    ('coupled processors near-miss', coupled_processors(4, 2, 6, 7, 12, 6)),
    ('coupled processors near-miss slow', coupled_processors(5, 3, 4, 4, 14, 5)),
    ('coupled processors critical', cp_own_at_branch(1, 1, F(9, 4), F(3, 2), F(5, 2))[0]),
    ('coupled processors critical', cp_own_at_branch(2, 1, F(16, 9), F(5, 4), 3)[0]),
    ('two-demand paired only', two_demand(0, 0, 1, 5, 5)),
    ('two-demand critical', two_demand(1, 1, 2, 9, 7)),
    ('two-demand critical', two_demand(3, 0, 4, 8, 5)),
    ('two-demand near-miss', two_demand(4, 4, 1, 6, 11)),
    ('two-demand near-miss', two_demand(2, 3, 1, 10, 6)),
    ('two-demand heavy traffic', two_demand(1, 2, 2, F(31, 10), F(41, 10))),
    ('planted own pole at branch point', planted('own_branch', 1, 'x_boundary', '-1/2')),
    ('planted own pole at branch point, heavy', planted('own_branch', 12, 'x_boundary', '-1/2', lo=1.01, hi=1.05, den=400, ylo=0.97, yhi=1.03)),
    ('planted induced pole at branch point', planted('other_branch', 2, 'x_boundary', '-1/2')),
    ('planted induced pole at branch point', planted('other_branch', 22, 'x_boundary', '-1/2')),
    ('planted double pole', planted('double_pole', 3, 'x_boundary', '1')),
    ('planted double pole', planted('double_pole', 33, 'x_boundary', '1')),
    ('planted double pole, heavy', planted('double_pole', 34, 'x_boundary', '1', lo=1.01, hi=1.06, den=400, ylo=1.005, yhi=1.06)),
    ('planted two poles at branch point', planted('both_branch', 5, 'x_boundary', '0')),
    ('planted marginal double pole', planted('marg_double', 6, 'x_marginal', '1')),
    ('planted marginal double pole', planted('marg_double', 66, 'x_marginal', '1')),
    ('planted interior pole at branch point', planted('marg_branch', 7, 'x_marginal', '-1/2')),
    ('planted interior pole at branch point', planted('marg_branch', 77, 'x_marginal', '-1/2')),
    ('random, drift (+,-)', rand_generic(201, lambda s, r: drift(s['int'])[0] > 0)),
    ('random, drift (-,+)', rand_generic(202, lambda s, r: drift(s['int'])[1] > 0)),
    ('random, interior pole cancelled', rand_generic(203, lambda s, r: drift(s['int'])[0] < 0 and str(r['x_boundary'][1]) == '-3/2' and str(r['x_marginal'][1]) == '-3/2')),
    ('random, interior pole dominant', rand_generic(204, lambda s, r: str(r['x_boundary'][1]) == '-3/2' and str(r['x_marginal'][1]) == '0')),
]


def answers(s, wid):
    w = walk_json(s, wid)
    a = Q.fmt(Q.analyse(Q.parse_walk(w)))
    for b in (A.solve(w), E.solve(w)):
        for k in a:
            assert a[k]['kappa'] == b[k]['kappa'], (wid, k, a[k], b[k])
            assert abs(F(a[k]['rho']) / F(b[k]['rho']) - 1) < F(1, 10 ** 20), (wid, k)
    return w, a


def main():
    for name, s in EXAMPLES + HELD:
        assert ergodic(s) and nondeg(s), name
        print('ok', name, flush=True)
    ex_w, ex_a = [], {}
    for i, (name, s) in enumerate(EXAMPLES):
        wid = 'e%d' % (i + 1)
        w, a = answers(s, wid)
        ex_w.append(w); ex_a[wid] = a
    rng = random.Random(2026)
    order = list(range(len(HELD)))
    rng.shuffle(order)
    ho_w, ho_a, prov = [], {}, []
    for j, i in enumerate(order):
        name, s = HELD[i]
        wid = 'w%02d' % (j + 1)
        w, a = answers(s, wid)
        ho_w.append(w); ho_a[wid] = a
        prov.append({'id': wid, 'source': name, 'answers': {k: [v['rho'][:12], v['kappa']] for k, v in a.items()}})
    json.dump({'walks': ex_w}, open(TASK + '/environment/examples.json', 'w'), indent=1)
    json.dump(ex_a, open(TASK + '/environment/examples_answers.json', 'w'), indent=1)
    json.dump({'walks': ho_w}, open(TASK + '/tests/heldout_walks.json', 'w'), indent=1)
    json.dump(ho_a, open(TASK + '/tests/expected.json', 'w'), indent=1)
    json.dump(prov, open('provenance.json', 'w'), indent=1)
    pickle.dump({'examples': EXAMPLES, 'held': [(HELD[i][0], HELD[i][1], 'w%02d' % (j + 1)) for j, i in enumerate(order)]},
                open('sets.pkl', 'wb'))
    from collections import Counter
    print(Counter((k, v['kappa']) for a in ho_a.values() for k, v in a.items()))


if __name__ == '__main__':
    main()
