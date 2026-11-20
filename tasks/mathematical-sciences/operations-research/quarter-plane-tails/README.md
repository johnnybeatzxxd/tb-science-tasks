# quarter-plane-tails

Write a program that returns the exact tail asymptotics (decay rate $\rho$ and polynomial exponent $\kappa$) of the boundary and marginal stationary probabilities of two-dimensional reflected random walks on the quarter plane, for walks it has not seen.

| | |
|---|---|
| **Author** | Eishiku Nuro |
| **Organization** | Turing |
| **Email** | *(to be filled in by the author)* |
| **Profile** | *(to be filled in by the author)* |
| **Conflicts of interest** | Paid contributor through Turing for this evaluation project. |
| **Domain** | mathematical-sciences / operations-research / exact tail asymptotics of two-dimensional reflected random walks (queueing networks) |
| **Agent budget** | 18,000 s |
| **Program limits** | separate container, no network, unprivileged user, 4 CPUs · 8 GB · 4 GB disk, 1800 s wall clock |

See [instruction.md](instruction.md) for the task as the agent receives it, and [task.toml](task.toml) for the environment and verifier configuration.

## Runs

| Run | Date (UTC) | Wall time | Reward | Record |
|---|---|---|---|---|
| Harbor oracle (`harbor run -a oracle`) | HARBOR_ORACLE_DATE | HARBOR_ORACLE_WALL | HARBOR_ORACLE_REWARD | job `HARBOR_ORACLE_JOB` |
| Harbor nop (`harbor run -a nop`) | HARBOR_NOP_DATE | HARBOR_NOP_WALL | HARBOR_NOP_REWARD | job `HARBOR_NOP_JOB` |
| Reference, solve stage offline (`solve.sh` with `--network none`), real verifier | RR_OFF_DATE | RR_OFF_WALL | 1 | `tests/provenance/run_records/reference_offline_solve.json` |
| Reference, real verifier, run 1 / run 2 | RR1_DATE | RR1_WALL | 1 / 1 | `reference_run1.json`, `reference_run2.json` (intermediates byte-identical) |
| nop, real verifier | NOP_DATE | NOP_WALL | 0 | `tests/provenance/run_records/nop.json` |

The reference program needs about 3 s for the 31 walks, which is under 1% of the 1800 s limit.

## The problem

A nearest-neighbour random walk on $\mathbb Z_+^2$ is the standard model of a two-node queueing network. It has one jump law in the interior, one on each axis and one at the origin. Tandem and Jackson networks, coupled processors and parallel queues with paired arrivals are all of this form once uniformised.

Except in product-form cases the stationary distribution $\pi$ has no closed form, but its tails are known exactly:

- **Kernel method** (Fayolle, Iasnogorodski and Malyshev): analytic continuation of the generating functions of the boundary probabilities along the kernel curve $K(x,y) = xy(\varphi(x,y) - 1) = 0$.
- **Convex level curves in log coordinates** (Miyazawa 2009; Kobayashi and Miyazawa): the same answer, described geometrically.

For each walk the program returns $(\rho, \kappa)$ in $a_n \sim C n^\kappa \rho^n$ for four sequences:

- the boundary probabilities $\pi(n,0)$ and $\pi(0,n)$;
- the marginals $P(L_1=n)$ and $P(L_2=n)$, the queue-length distributions of the two stations.

## Difficulty

**Crux.** The exponent and the rate are decided by which of several competing singularities of the boundary generating functions comes first and how they meet. This involves:

- the branch point of the kernel;
- poles on the correct branch;
- a pole induced from the other axis;
- an interior pole of the marginal that is cancelled whenever it lies on the lower branch of the kernel curve.

The coincidences of these points, which change $\kappa$, occur at natural parameters of standard models.

**Why an expert meets these instances.** All of them come up in ordinary queueing work:

- Critical cases come from small integer rates. One example is parallel queues with paired arrivals $(\lambda_1,\lambda_2,\lambda_{12},\mu_1,\mu_2) = (1,1,2,9,7)$: there a boundary pole sits exactly on the branch point ($\kappa = -1/2$), while each station is an M/M/1 queue.
- Another is coupled processors whose boundary service rate sits on a regime boundary.
- Heavy traffic ($\rho$ up to 0.98) is the regime queueing studies care about.
- Near-coincidences (relative gaps $3\times10^{-5}$–$10^{-3}$) appear in about one random two-queue model in ten.

**What goes wrong.** Each pitfall leaves an internally consistent answer:

- **Truncate the plane, solve, fit the tail.** At near-coincidences the computed tail shows a steady, resolution-independent exponent that is wrong. Examples: $\kappa_n \approx -0.39$ where $\kappa = 0$, and $\kappa_n \approx +0.95$ where $\kappa = 0$. In heavy traffic the required truncation is out of reach.
- **The common partial versions of the classification.** These are:
  - own pole versus branch point only;
  - no induced pole;
  - marginal rate $\min(x_K, x^*)$;
  - no merging of coincident points.

  Each of them agrees with numerics on random light-traffic walks, which almost never sit on a coincidence.

## Reference solution

`solution/qtails.py` is installed by `solve.sh` as `/root/qtails/tails.py`. It works with exact rational input and 80-digit arithmetic.

1. **Kernel.** It forms $K = a(x)y^2 + b(x)y + c(x)$ and $D = b^2 - 4ac$. The branch point $x_3$ is the first real zero of $D$ to the right of 1.
2. **Own poles.** These are the real roots in $(1, x_3]$ of $aN_1^2 + bN_1D_1 + cD_1^2$, after exact deflation of $x = 1$, where $y = N_1/D_1$ is the zero set of the boundary kernel. A root counts only if $N_1/D_1 = Y_0(x)$, the lower root.
3. **Induced pole.** It is the smallest $x \in (1, x_3]$ with $Y_0(x) = R_2$, where $R_2$ is the first singularity of the other axis's function, provided it is a pole. The two axes are iterated to a fixed point.
4. **Boundary exponent.** If $x^* < x_3$, then $\kappa = (\text{number of poles at } x^*) - 1$. If $x^* = x_3$, then $\kappa = -3/2, -1/2, 0$ for zero, one or two poles there.
5. **Marginal.** The interior pole $x_K = P_-/P_+$ is rational, and the other root $c(x_K)/a(x_K)$ of $K(x_K, \cdot)$ is rational too. Comparing that root with 1 decides exactly whether $(x_K, 1)$ lies on the upper branch, on the lower branch, or at the rightmost point:
   - **Upper branch.** $x_K$ is a pole, and $\kappa_{\rm marg} = \kappa_{\rm bdry} + 1$ when it coincides with a boundary pole.
   - **Lower branch.** The pole is cancelled by the kernel identity.
   - **Rightmost point.** The local exponent in $s = \sqrt{x_3 - x}$ is $-1 + \min(e, 0)$.

Independent alternatives, both passing the real verifier, are in `tests/provenance/alternatives/`:

- `alt_theta.py`, log-coordinate convex geometry with bisection and Newton steps, no polynomial roots;
- `alt_exact.py`, exact real algebraic arithmetic in sympy, with coincidences decided exactly.

## Verification

`tests/test.sh` and the generated `tests/test_outputs.py` (built by `gen_tests.py` from `test_outputs_head.py`; the checking logic is in `qtails_check.py`) work as follows.

**Setup.**

- `reward.txt` is set to 0 first.
- `/logs/verifier` is restricted to root and `/tests` is made unreadable to other users.

**Submission handling.**

- `/root/qtails` is walked with `lstat`; symbolic links and special files are rejected.
- `*.pyc` files and `__pycache__` directories are deleted, so only source runs.

**Running the program.**

- It runs once on the 31 walks as user `sandbox`.
- It gets a fresh, empty working directory, which is also `HOME` and `TMPDIR`.
- Its input and output are in a separate private directory, and both directories are removed afterwards.
- On timeout and at exit, its process group and all `sandbox` processes are killed.

**Reading the output.**

- The file is read with `lstat`, `S_ISREG`, `O_NOFOLLOW | O_NONBLOCK` and `fstat`, and must be at most 1 MB.
- It is parsed as strict JSON: duplicate keys, `NaN`/`Infinity` and non-string fields are rejected.

**Tests.** `test_contract` comes first, followed by one test per walk (`test_w01` … `test_w31`). `intermediates.json` records, per walk and sequence, the reported values, the relative error and the match flags, with no timings.

**Constants.**

- **$\rho$ tolerance $10^{-9}$ relative.** $\rho$ is algebraic of degree at most 6. A plain double-precision implementation of the exact characterisation reaches $7.6\times10^{-15}$ on this file (`float64_control`), so the tolerance leaves a margin of more than $10^5$ and only asks for a correct answer to roughly nine digits.
- **At least 15 significant digits.** A decimal string must be able to carry $10^{-9}$ relative accuracy with margin. Double precision prints 15–17 digits.
- **1800 s.** This is about 600 times the reference's 3 s, enough for slower exact-arithmetic implementations (the sympy alternative needs about 10 s).
- **1 MB output cap.** The reference output is about 14 kB.

## Held-out set

The 31 walks (124 $(\rho,\kappa)$ pairs) appear in random order with opaque ids:

- **Classical networks at natural rates:** Jackson networks with feedback, tandem networks, coupled processors, and parallel queues with single and paired arrivals, including heavy-traffic versions.
- **Exact regime boundaries:** pole at the branch point (own and induced), double poles, two poles at the branch point, interior pole meeting a boundary pole, and interior pole at the rightmost point.
- **Near-coincidences:** ten walks with relative gaps $3\times10^{-5}$–$10^{-3}$.
- **Positive interior mean component:** twelve walks.

Every property stated in the instruction is asserted on this file by `tests/provenance/check_promises.py`.

## Provenance and controls (`tests/provenance/`)

- **`check_promises.py` / `.txt`.** It asserts on the graded file:
  - formats and exact sums;
  - drift and support conditions, positive recurrence, irreducibility and aperiodicity;
  - the denominator, support and $\rho$ ranges;
  - the presence of each named classical network;
  - the counts of exact regime boundaries, near-coincidences and positive-mean walks;
  - that the reference and the exact-arithmetic solver reproduce `expected.json`.
- **`check_references.py` / `.txt`.** Independent principles:
  - exact algebraic candidates for every walk (coincidences shown as the same root of the same irreducible polynomial);
  - the M/M/1 marginals of the paired-arrival walks;
  - subtraction-free block-GTH truncations with the local exponent $\kappa_n$.
- **`check_literature.py` / `.txt`.** It reproduces two published anchors: the Jackson (1957) product form on 60 random networks, and the M/M/1 marginals of the Flatto–Hahn (1984) paired-arrival model on 120 random instances.
- **`probe_boundaries.py` / `.txt`.** Edge inputs the instruction allows all run without error and agree with the exact solver: support 4, $\rho \approx 0.99$, both drift-sign patterns, 7-digit denominators and single-jump boundary laws.
- **`check_controls.py` / `.txt`.** It runs on the checker the verifier uses. The reference output and an output within tolerance are correct. Every other control is incorrect: empty file, empty object, the example output, $\rho$ just past tolerance, dropped walk, spurious walk, $\kappa$ off by 1/2, numeric `rho`, boolean `kappa`, duplicate key, `NaN`, a 12-digit $\rho$, and the weak baselines below.
- **`run_records/`.** Real-verifier records with stdout and intermediates for the reference (two runs and the offline solve), nop, both alternatives, the float64 control, and a symlinked submission.

| Control (real verifier or shared checker) | Result |
|---|---|
| reference, ×2 + offline solve | 1, intermediates byte-identical |
| alternatives (θ-geometry, exact arithmetic), float64 complete theory | 1 |
| nop; symlinked `tails.py` | 0 |
| truncate-and-fit (block GTH, $N = 300$, Richardson, $\kappa$ rounded to 1/2) | incorrect |
| own poles + branch point only, marginal $\min(x_K, x^*)$ | incorrect |
| complete except the induced pole | incorrect |
| complete except the marginal cancellation rule | incorrect |
| complete except merging coincident singularities | incorrect |

## Reproduction

The pinned versions are Python 3.12.7 (`python:3.12.7-slim-bookworm`), numpy 2.1.3, scipy 1.14.1, sympy 1.13.3, mpmath 1.3.0, pytest 8.4.1 and Harbor 0.26.0. The checks use fixed seeds: check_literature uses 1957, and the held-out order was shuffled with 2026.

```
harbor run -p <task-dir> -a oracle
harbor run -p <task-dir> -a nop
cd tests/provenance
python3 check_promises.py
python3 check_references.py --numeric
python3 check_literature.py
python3 probe_boundaries.py
python3 check_controls.py
```
