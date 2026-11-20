"""Subtraction-free (GTH-type) stationary distribution of a truncated 2-D reflected
nearest-neighbour random walk on {0..N} x {0..M}.

Walk spec: dict with keys 'int', 'x', 'y', 'o', each a dict {(a,b): prob}.
  'int' : interior (i>=1, j>=1), a,b in {-1,0,1}
  'x'   : x-axis   (i>=1, j=0),  a in {-1,0,1}, b in {0,1}
  'y'   : y-axis   (i=0, j>=1),  a in {0,1}, b in {-1,0,1}
  'o'   : origin,                a,b in {0,1}
Jumps that leave the truncation box are clipped back onto its boundary.
Levels = i (x coordinate), phases = j.  Returns pi as (N+1, M+1) array.
"""
import numpy as np


def law(spec, i, j):
    if i >= 1 and j >= 1:
        return spec['int']
    if i >= 1 and j == 0:
        return spec['x']
    if i == 0 and j >= 1:
        return spec['y']
    return spec['o']


def blocks(spec, N, M):
    """Return lists D[i] (i->i-1), T[i] (i->i), U[i] (i->i+1) as dense arrays."""
    m = M + 1
    D = [None] * (N + 1)
    T = [None] * (N + 1)
    U = [None] * (N + 1)
    for i in range(N + 1):
        Di = np.zeros((m, m)); Ti = np.zeros((m, m)); Ui = np.zeros((m, m))
        for j in range(m):
            for (a, b), p in law(spec, i, j).items():
                if p == 0:
                    continue
                ii, jj = i + a, j + b
                if ii < 0 or jj < 0:
                    raise ValueError('law leaves quadrant at %r' % ((i, j, a, b),))
                ii, jj = min(ii, N), min(jj, M)   # clip jumps leaving the box
                tgt = {-1: Di, 0: Ti, 1: Ui}[ii - i]
                tgt[j, jj] += p
        D[i], T[i], U[i] = Di, Ti, Ui
    return D, T, U


class Elim:
    """GTH elimination of the transient block T with absorbing outflow mass e
    (row deficit).  Stores rows/cols/pivots so that x (I-T) = b can be solved
    subtraction-free afterwards."""

    def __init__(self, T, exitmass):
        A = T.copy()
        np.fill_diagonal(A, 0.0)
        e = exitmass.copy()
        n = A.shape[0]
        self.n = n
        self.rows = []
        self.cols = []
        self.piv = np.zeros(n)
        for k in range(n):
            d = A[k, k + 1:].sum() + e[k]
            self.piv[k] = d
            r = A[k, k + 1:].copy()     # k -> later states
            c = A[k + 1:, k].copy()     # later states -> k
            self.rows.append(r)
            self.cols.append(c)
            if k + 1 < n:
                # Schur complement: later states get k's out-transitions
                A[k + 1:, k + 1:] += np.outer(c, r / d)
                e[k + 1:] += c * (e[k] / d)
            # diagonal entries created by the update are re-zeroed (self loops do not matter
            # in GTH: they cancel from both sides)
            if k + 1 < n:
                idx = np.arange(k + 1, n)
                A[idx, idx] = 0.0

    def left_solve(self, b):
        """x (I - T) = b  for b >= 0."""
        n = self.n
        b = b.astype(float).copy()
        for k in range(n):
            if k + 1 < n:
                b[k + 1:] += b[k] * self.rows[k] / self.piv[k]
        x = np.zeros(n)
        for k in range(n - 1, -1, -1):
            s = b[k]
            if k + 1 < n:
                s += x[k + 1:] @ self.cols[k]
            x[k] = s / self.piv[k]
        return x

    def right_solve(self, B):
        """(I - T) X = B  for B >= 0 (columns)."""
        n = self.n
        B = B.astype(float).copy()
        for k in range(n):
            if k + 1 < n:
                B[k + 1:] += np.outer(self.cols[k], B[k] / self.piv[k])
        X = np.zeros_like(B)
        for k in range(n - 1, -1, -1):
            s = B[k].copy()
            if k + 1 < n:
                s += self.rows[k] @ X[k + 1:]
            X[k] = s / self.piv[k]
        return X


def gth_stationary(P):
    P = P.copy()
    n = P.shape[0]
    np.fill_diagonal(P, 0.0)
    for k in range(n - 1, 0, -1):
        s = P[k, :k].sum()
        P[:k, k] /= s
        P[:k, :k] += np.outer(P[:k, k], P[k, :k])
        idx = np.arange(k)
        P[idx, idx] = 0.0
    x = np.zeros(n); x[0] = 1.0
    for k in range(1, n):
        x[k] = x[:k] @ P[:k, k]
    return x / x.sum()


def stationary(spec, N, M):
    D, T, U = blocks(spec, N, M)
    m = M + 1
    Tc = [None] * (N + 1)
    El = [None] * (N + 1)
    Tc[N] = T[N]
    for i in range(N, 0, -1):
        ex = D[i].sum(axis=1)               # censored chain on levels <= i: exits from level i
        El[i] = Elim(Tc[i], ex)
        W = El[i].right_solve(D[i])         # (I-T_i)^{-1} D_i, stochastic
        Tc[i - 1] = T[i - 1] + U[i - 1] @ W
    # level 0 censored chain is stochastic
    pi0 = gth_stationary(Tc[0])
    pis = [pi0]
    for i in range(1, N + 1):
        b = pis[-1] @ U[i - 1]
        pis.append(El[i].left_solve(b))
    P = np.array(pis)
    return P / P.sum()
