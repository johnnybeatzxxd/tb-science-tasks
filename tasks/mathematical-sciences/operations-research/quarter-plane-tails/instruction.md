Write a program that returns the exact tail asymptotics of the stationary distribution of two-dimensional reflected random walks on the quarter plane, for walks it has not seen.

**The walks.** A walk $L = (L_1, L_2)$ lives on $\{0,1,2,\dots\}^2$. At each step it adds a jump $(a, b)$ with $a, b \in \{-1, 0, 1\}$. The law of the jump depends only on the region of the current state:

- `interior`: $L_1 \ge 1$ and $L_2 \ge 1$;
- `x_axis`: $L_1 \ge 1$ and $L_2 = 0$;
- `y_axis`: $L_1 = 0$ and $L_2 \ge 1$;
- `origin`: $L_1 = L_2 = 0$.

A boundary law never moves the walk out of the quadrant. All probabilities are rational numbers. Every walk you will be given is irreducible, aperiodic and positive recurrent. The mean of its interior law is nonzero in both coordinates. For each coordinate, its interior law gives positive probability to some jump that decreases that coordinate and to some jump that increases it. Let $\pi$ be the stationary distribution. For each walk, four sequences are asked for:

- `x_boundary`: $\pi(n, 0)$, $n \ge 1$;
- `y_boundary`: $\pi(0, n)$, $n \ge 1$;
- `x_marginal`: $P(L_1 = n) = \sum_{j \ge 0} \pi(n, j)$;
- `y_marginal`: $P(L_2 = n) = \sum_{i \ge 0} \pi(i, n)$.

For every walk you will be given, each of these sequences $a_n$ satisfies $a_n \sim C\, n^{\kappa} \rho^{n}$ as $n \to \infty$, with constants $C > 0$, $0 < \rho < 1$ and real $\kappa$. For each walk and each sequence, your program must return $\rho$ and $\kappa$.

**Program interface.** Put your program at `/root/qtails/tails.py`. It is run as

```
python3 /root/qtails/tails.py INPUT.json OUTPUT.json
```

`INPUT.json` has the form

```json
{"walks": [{"id": "w1",
            "interior": {"-1,0": "3/10", "1,0": "1/5", "0,-1": "1/4", "0,1": "1/8", "0,0": "1/8"},
            "x_axis":   {"-1,0": "1/2", "1,0": "1/5", "0,1": "1/8", "0,0": "7/40"},
            "y_axis":   {"0,-1": "1/2", "1,0": "1/5", "0,1": "1/8", "0,0": "7/40"},
            "origin":   {"1,0": "1/5", "0,1": "1/8", "0,0": "27/40"}}]}
```

Each law maps a jump `"a,b"` to its probability, written as an exact fraction string. Jumps that are not listed have probability zero. Your program must write `OUTPUT.json` as an object keyed by walk id:

```json
{"w1": {"x_boundary": {"rho": "...", "kappa": "..."},
        "y_boundary": {"rho": "...", "kappa": "..."},
        "x_marginal": {"rho": "...", "kappa": "..."},
        "y_marginal": {"rho": "...", "kappa": "..."}}}
```

`rho` is a decimal string with at least 15 significant digits. `kappa` is the exact value, written as an integer or a fraction such as `"2"` or `"-5/3"`; a finite decimal such as `"-0.25"` is also accepted.

`/root/examples.json` contains a few example walks in the input format, and `/root/examples_answers.json` contains their answers in the output format.

**Verification.** The verifier copies `/root/qtails/` into a fresh container without network access. That container has the same operating system, Python and Python packages as this environment had at the start. Nothing you install now carries over. It runs your program once on a held-out file of walks that you are not given, with 4 CPUs, 8 GB of memory and a wall-clock limit of 1800 seconds for the whole file. The task passes only if the program finishes within the limit and, for every walk in the held-out file and each of its four sequences, the returned `kappa` equals the exact value and the returned `rho` agrees with the exact value to a relative error of at most $10^{-9}$; any missing, malformed or wrong entry fails the task.

You have 18000 seconds to complete this task. Do not cheat by using online solutions or hints specific to this task.
