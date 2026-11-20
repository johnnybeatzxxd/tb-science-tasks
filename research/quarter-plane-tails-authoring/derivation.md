# quarter-plane-tails — derivation notes for the reference classification

These notes record the argument behind `solution/qtails.py`, the checks of each step, and the cases that were found to need care.

## Setup

The jump laws are $p$ (interior), $p^{(1)}$ (x-axis), $p^{(2)}$ (y-axis) and $p^{(0)}$ (origin), with generating functions $\varphi, \varphi_1, \varphi_2, \varphi_0$. The kernels are $K = xy(\varphi - 1)$, $K_i = xy(\varphi_i - 1)$.

The unknowns are $Q(x,y) = \sum_{i,j\ge1}\pi_{ij}x^iy^j$, $Q_1(x) = \sum_{i\ge1}\pi_{i0}x^i$, $Q_2(y)$ and $\pi_{00}$. The balance equations give

$$K(x,y)Q(x,y) + K_1(x,y)Q_1(x) + K_2(x,y)Q_2(y) + K_0(x,y)\pi_{00} = 0 .$$

On the branch $y = Y_0(x)$ of $K = 0$ (the smaller root), this continues $Q_1$ along $(1, x_3]$:

$$Q_1(x) = -\frac{K_2(x,Y_0)Q_2(Y_0) + K_0(x,Y_0)\pi_{00}}{K_1(x,Y_0)} .$$

## Boundary singularities

The first singularity $x^*$ of $Q_1$ is the smallest of three candidates:

1. **The branch point $x_3$**, where $D(x_3) = 0$. There $Q_1 = A + Bs + \dots$ with $s = \sqrt{x_3 - x}$, so $\kappa = -3/2$.
2. **Own poles**, the zeros of $K_1(x, Y_0(x))$. Zeros on the branch $Y_1$ are not singularities.
3. **The induced pole** $x = X_1(y_p)$, where $y_p$ is a pole of $Q_2$. It counts only if $y_p \le Y_0(x_3)$.

The exponent depends on how the candidates meet:

- At a single pole, $\kappa = 0$. A double coincidence gives a pole of order 2, so $\kappa = 1$.
- At the branch point, a pole contributes $1/s$, so one pole gives $\kappa = -1/2$ and two give $1/s^2$, a simple pole, so $\kappa = 0$.

Induced-of-induced candidates lie further out and never matter.

## Marginal

$P(L_1 = n)$ has generating function $Q_1 + Q(x,1) + \text{const}$, and

$$Q(x,1) = -\frac{(P^{(1)}_{+}x - P^{(1)}_{-})Q_1 + x\,c_0}{P_+(x - x_K)}, \qquad x_K = P_-/P_+ .$$

The other root of $K(x_K,\cdot)$ besides 1 is $y_o = c(x_K)/a(x_K)$, a rational number. It decides the cases:

- **$y_o < 1$.** Then $(x_K,1)$ lies on the upper branch. The numerator does not vanish, so $x_K$ is a pole. If it coincides with a pole of order $m$ of $Q_1$, the order becomes $m+1$.
- **$y_o > 1$.** Then $(x_K,1)$ lies on the lower branch. The continued kernel identity makes the numerator vanish, so the pole is cancelled and the marginal decays at the boundary rate. (Numerically, 8 of 13 random walks with $x_K < x^*$ fell in this case; a naive $\min(x_K, x^*)$ is wrong for them.)
- **$y_o = 1$.** Then $x_K = x_3$, and the numerator is $O(s^{1+\min(e,0)})$ where $Q_1 \sim s^e$. So the marginal behaves like $s^{-1+\min(e,0)}$, giving $\kappa = -1/2$, $0$ or $1/2$ for $e = 1, -1, -2$.

  An earlier version gave $\kappa = -1/2$ regardless of $e$. It was caught by the exact M/M/1 marginals of the paired-arrival model (for example $(0,0,1,5,5)$ and $(1,1,2,9,7)$, where the boundary has $e = -1$) and corrected before the held-out set was frozen.

## Validation summary

- Random ergodic walks of all drift-sign patterns, about 900 of them, were checked against block-GTH truncations. Every disagreement traced to a close competitor (gap below 3%) or to a truncation in the direction that feeds an induced pole. Enlarging that direction removes it.
- Exact product forms reproduce the answers: Jackson networks with feedback, tandem networks, and the marginals of the paired-arrival model (181 instances).
- Planted instances of every category show the local exponent converging to the predicted value.
- Three implementations agree on all of these: kernel-method/polynomial, log-coordinate/bisection, and exact algebraic.

## Excluded on purpose

The following do not appear in the held-out set:

- **Zero drift in one interior coordinate**, as in a tandem queue with $\mu_1 = \mu_2$. The branch point sits at 1 and the numerical evidence was not clean enough.
- **Own double zeros (tangencies).** A generator exists, but no admissible instance was found in the search budget.
- **Walks without a jump in some direction in the interior.** These are excluded by the instruction.
