# quarter-plane-tails

Write a program that returns the exact tail asymptotics (decay rate $\rho$ and polynomial exponent $\kappa$) of the boundary and marginal stationary probabilities of two-dimensional reflected random walks on the quarter plane, for walks it has not seen.

| | |
|---|---|
| **Author** | Eishiku Nuro |
| **Domain** | mathematical-sciences / operations-research / exact tail asymptotics of two-dimensional reflected random walks (queueing networks) |
| **Agent budget** | 5 hours (18,000 s) |
| **Verifier** | separate container, no network, 4 CPUs · 8 GB, 1800 s wall clock for the submitted program |

See [instruction.md](instruction.md) for the task as the agent receives it, and [task.toml](task.toml) for the environment and verifier configuration.

## The problem

A nearest-neighbour random walk on $\mathbb Z_+^2$ is the standard model of a two-node queueing network. It has one jump law in the interior, one on each axis and one at the origin. Tandem and Jackson networks, coupled processors and parallel queues with paired arrivals are all of this form once uniformised. Except in product-form cases the stationary distribution $\pi$ has no closed form, but its tails are known exactly. They come from the analytic continuation of the generating functions of the boundary probabilities along the kernel curve $K(x,y) = xy(\varphi(x,y) - 1) = 0$, where $\varphi$ is the generating function of the interior jump law. This is the kernel method of Fayolle, Iasnogorodski and Malyshev. Miyazawa and Kobayashi–Miyazawa give the same answer as a description of convex level curves in log coordinates.

For each walk the program must return the pair $(\rho, \kappa)$ in $a_n \sim C n^\kappa \rho^n$ for four sequences:

- the boundary probabilities $\pi(n,0)$ and $\pi(0,n)$;
- the marginals $P(L_1 = n)$ and $P(L_2 = n)$, the queue-length distributions of the two stations.

## Why the task is hard

The answer is not a formula but a case analysis of the singularities of the boundary generating function $Q_1(x) = \sum_n \pi(n,0) x^n$ on $(1, x_3]$. Several mechanisms compete there, and the exponent records how they meet:

- **The branch point $x_3$ of the kernel**, where the two roots $Y_0 \le Y_1$ of $K(x,\cdot)$ merge. If it comes first, $\kappa = -3/2$, not a pole. This happens on an open set of walks.
- **Own poles.** These are zeros of $K_1(x, Y_0(x))$, the boundary kernel evaluated on the *lower* branch. Zeros on the upper branch $Y_1$ are not singularities.
- **The induced pole.** A pole $y_p$ of the *other* boundary function $Q_2$ reaches $Q_1$ at $x = X_1(y_p)$, but only if $y_p$ lies below the height $Y_0(x_3)$ of the rightmost point of the kernel curve.
- **Coincidences.** Two poles at the same point give $\kappa = 1$. A pole at the branch point gives $\kappa = -1/2$, and two poles there give $\kappa = 0$.
- **The marginal.** Its generating function adds a pole at the interior root $x_K$ of $K(x, 1) = 0$. That pole is real only when $(x_K, 1)$ lies on the upper branch $Y_1$. On the lower branch the kernel identity cancels it, and the station's queue length decays at the boundary rate instead. When $x_K$ meets the boundary singularity, the exponents combine: $\kappa_{\rm marg} = \kappa_{\rm bdry} + 1$ on the upper branch, and when $(x_K, 1)$ is the rightmost point of the curve, the marginal's local exponent is $-1 + \min(e, 0)$ in $s = \sqrt{x_3 - x}$.

All of these are real. They occur at natural parameters of standard models, not only in planted instances:

- In the parallel-queue model with paired arrivals (Flatto–Hahn, Wright), integer rates such as $(\lambda_1, \lambda_2, \lambda_{12}, \mu_1, \mu_2) = (1, 1, 2, 9, 7)$ put a boundary pole exactly on the branch point ($\kappa = -1/2$). Each marginal is nevertheless exactly geometric, because each station is an M/M/1 queue.
- Coupled processors whose fast boundary service exactly balances the interior (a regime boundary) give $\kappa = -1/2$.
- In tandem networks the induced pole is the mechanism behind the product-form boundary rate.

**The traps are invisible to self-checks.**

- *Truncate the plane, solve, fit the tail.* This is the natural numerical route, and it fails in three ways.
  - In heavy traffic ($\rho \approx 0.97$–$0.99$, the regime queueing studies care about) the truncation needed is out of reach.
  - Close competitors are common at natural parameters. Random two-queue models routinely have two candidate singularities $10^{-3}$–$10^{-5}$ apart, or a pole just beyond the branch point on the second sheet. Then the asymptotic regime starts only at $n \gg 10^3$–$10^6$. Below that, the computed tail shows a steady, resolution-independent exponent that is wrong: for example $\kappa \approx +0.95$ where the truth is $0$, or $\kappa \approx -0.45$ where it is $-3/2$. Refining the truncation does not move it.
  - The fit cannot give $\rho$ to the stated accuracy.
- *Implement the textbook classification.* The common partial versions are internally consistent and agree with numerics on random light-traffic walks, which almost never sit on a coincidence. These versions are:
  - own pole versus branch point only;
  - forgetting the induced pole;
  - taking the marginal rate as $\min(x_K, x^*)$ without the cancellation rule;
  - not merging coincident singularities.

  Each fails on several held-out walks (see "Evidence").

## Reference solution

`solution/qtails.py` is installed by `solve.sh` as `/root/qtails/tails.py`. It works with exact rational input and 80-digit arithmetic.

1. **Kernel.** It forms the kernel $K = a(x)y^2 + b(x)y + c(x)$ and its discriminant $D = b^2 - 4ac$. The branch point $x_3$ is the first real zero of $D$ to the right of 1.
2. **Own poles.** These are the real roots in $(1, x_3]$ of $a N_1^2 + b N_1 D_1 + c D_1^2$, after exact deflation of the trivial root $x = 1$. Here $y = N_1/D_1$ is the zero set of the boundary kernel. A root counts only if $N_1/D_1$ equals the lower root $Y_0(x)$.
3. **Induced pole.** It is the smallest $x \in (1, x_3]$ with $Y_0(x) = R_2$, where $R_2$ is the first singularity of the other axis's function, provided that singularity is a pole. The two axes are iterated to a fixed point.
4. **Classification.** $\kappa = (\text{number of poles at } x^*) - 1$ if $x^* < x_3$. If $x^* = x_3$, then $\kappa = -3/2, -1/2, 0$ for zero, one or two poles there.
5. **Marginal.** The interior pole $x_K = P_{-1}/P_{+1}$ is rational, and the other root of $K(x_K, \cdot)$ is the rational $c(x_K)/a(x_K)$. Comparing it with 1 decides exactly whether $(x_K, 1)$ lies on the upper branch (a real pole), on the lower branch (cancelled), or at the rightmost point. The exponent rules above then give $\kappa$.

The program needs about one second per walk.

### Independent alternatives (both pass the real verifier)

- `alt_theta.py` (log-coordinate convex geometry). It locates the rightmost point by bisection on $\min_{\theta_2}\gamma(\theta_1, \theta_2)$, own and induced poles by bracketing and Newton iterations on exponential sums along the lower arc, and tangencies by minimising $|f|$. It uses no polynomial root finding.
- `alt_exact.py` (exact real algebraic arithmetic, sympy). All candidates are real roots of irreducible polynomials over $\mathbb Q$, isolated exactly. Coincidences are decided exactly (same irreducible factor, same root index), and branch membership by certified signs.

Both are kept with the authoring files. They agree with the reference on every held-out answer: $\kappa$ exactly and $\rho$ to $10^{-20}$.

### Independent truth checks (not sharing the kernel-method code)

- **Exact product forms.**
  - For Jackson networks with feedback and tandem networks, $\pi$ is explicit, and the answers ($\rho_i = \Lambda_i/\mu_i$, $\kappa = 0$ for all four sequences) are reproduced on 40 random networks and on the held-out ones.
  - In the paired-arrival model each marginal is exactly M/M/1. The reference gives $\rho = (\lambda_i + \lambda_{12})/\mu_i$ and $\kappa = 0$ on 181 random instances, including those whose boundary has $\kappa = -1/2$.
- **Subtraction-free numerics.** `gth2d.py` is a block Grassmann–Taksar–Heyman elimination of large truncations, which keeps relative accuracy down to $10^{-280}$. The local exponent $\kappa_n = n(a_{n+1}/(\rho a_n) - 1)$ is computed with the reference $\rho$, and it converges to the reference $\kappa$:
  - on several hundred random ergodic walks of all three drift-sign patterns;
  - on planted instances of every category;
  - on all light-traffic held-out walks.

  Where it does not, the cause is a close competitor or a truncation artefact, and enlarging the truncation in the relevant direction confirms the reference (see the evidence files).
- **Exact certificates for planted events.** Planted walks are constructed with rational coordinates of the coinciding points, so each event is checked in exact arithmetic. Examples: $D(x_3) = 0$, $\varphi_1(x_3, Y_3) = 1$, and $K(x^*, y^*) = 0$ together with $\varphi_1(x^*, y^*) = 1$ and $\varphi_2(X_0(y^*), y^*) = 1$.

## Held-out set

The held-out set has 31 walks and 124 $(\rho, \kappa)$ pairs, in random order with opaque ids:

- **Classical models at natural parameters:**
  - Jackson networks with feedback (one in heavy traffic, $\rho = 0.98$);
  - tandem networks (one in heavy traffic);
  - coupled processors (generic, near-miss and critical);
  - parallel queues with paired arrivals (critical, near-miss and heavy traffic).
- **Walks with planted structural events:** pole at the branch point (own and induced), double poles, two poles at the branch point, interior pole meeting a boundary pole, and interior pole at the rightmost point. These include heavy-traffic versions.
- **Random walks** with interior drift sign patterns $(-,-)$, $(+,-)$ and $(-,+)$, and with the interior pole either dominant or cancelled.

The four public examples in `/root/examples.json` cover only the generic cases.

## Verification

`tests/test_outputs.py` copies the held-out walks, runs `python3 /root/qtails/tails.py` once with a 1800 s limit, and checks every walk. For each of the four sequences:

- `kappa` must equal the reference exactly; it is parsed as an exact rational.
- `rho` must be within relative error $10^{-9}$ of the reference.

Malformed entries and missing walks fail. The reward is 1 only if every test passes. The program output is copied to `/logs/verifier/program_output.json` for audit.

The $\rho$ tolerance is not a separating lever. $\rho$ is an algebraic number of degree at most 6, and a double-precision implementation of the exact characterisation meets $10^{-9}$ with a margin of more than $10^3$. Methods without the characterisation fail on $\kappa$ (see below).

## Evidence

All runs use the real verifier (`tests/Dockerfile` image, `--network none`, 4 CPUs, 8 GB). The submission directory is mounted as `/root/qtails`. Logs and per-run program outputs are kept with the authoring files.

| Submission | Reward | Failed walk tests (of 31) |
|---|---|---|
| reference (`solve.sh` in the agent image, artifact copied to the verifier) | 1 | 0 |
| reference, three repeated runs | 1, 1, 1 | 0 — `program_output.json` byte-identical (sha256 `3f348c55…`) |
| alternative 1: log-coordinate geometry (`alt_theta.py`) | 1 | 0 |
| alternative 2: exact real algebraic arithmetic (`alt_exact.py`) | 1 | 0 |
| complete theory in IEEE double precision (numpy, coincidence tolerance $10^{-8}$; positive control) | 1 | 0 — worst relative $\rho$ error $7.6\times10^{-15}$ |
| no program (nop) | 0 | all |
| truncate-and-fit (block GTH, $N \ge 300$, Richardson fit, $\kappa$ rounded to a multiple of 1/2) | 0 | 28 |
| own poles and branch point only, marginal $= \min(x_K, x^*)$ | 0 | 23 |
| complete except the induced pole from the other axis | 0 | 7 |
| complete except the marginal cancellation rule | 0 | 21 |
| complete except merging of coincident singularities | 0 | 31 |

Boundary probes on the reference output:

- every $\rho$ scaled by $1 + 5\times10^{-10}$ passes;
- one $\rho$ scaled by $1 + 2\times10^{-9}$ fails;
- $\kappa$ written as decimals (`-1.5`) passes;
- one $\kappa$ shifted by 1/2 fails;
- one walk missing fails;
- one $\rho$ with 12 significant digits fails.

**Independent numerical check of the held-out set.** Each walk is solved by subtraction-free block GTH on an $N \times N$ truncation, with $N = 200$–$600$ according to the slowest rate. The local exponent $\kappa_n$ is computed with the reference $\rho$. For the product-form, critical and planted walks it converges to the reference $\kappa$; for example $-0.494$ ($-1/2$), $+0.956$ ($1$) and $0.000$ ($0$).

In seven walks one sequence has a close competing singularity: a relative gap of $2\times10^{-4}$–$6\times10^{-4}$ between a pole and the branch point, or between the interior and boundary poles. There the truncation shows a steady intermediate exponent, as described under "Why the task is hard". For example, w16 has $\kappa_n \approx -0.39$ on a sequence whose exponent is $0$, because its own pole lies $2.3\times10^{-4}$ below the branch point. In these walks the three solvers agree, and the gap is reported by `near.py`.
