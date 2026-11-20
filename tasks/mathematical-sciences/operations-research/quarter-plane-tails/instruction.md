Write a program that returns the exact tail asymptotics of the stationary distribution of two-dimensional reflected random walks on the quarter plane.

**The walks.** A walk $ L = (L_1, L_2) $ lives on $ \{0,1,2,\dots\}^2 $. At each step it adds a jump $ (a, b) $ with $ a, b \in \{-1, 0, 1\} $. The law of the jump depends only on the region of the current state:

- `interior`: $ L_1 \ge 1 $ and $ L_2 \ge 1 $;
- `x_axis`: $ L_1 \ge 1 $ and $ L_2 = 0 $;
- `y_axis`: $ L_1 = 0 $ and $ L_2 \ge 1 $;
- `origin`: $ L_1 = L_2 = 0 $.

A boundary law never moves the walk out of the quadrant. Every walk of an input file has these properties:

- all probabilities are rational;
- the walk is irreducible, aperiodic and positive recurrent;
- the mean of its interior law is nonzero in both coordinates;
- for each coordinate, its interior law gives positive probability to some jump that decreases that coordinate and to some jump that increases it.

Let $ \pi $ be the stationary distribution. For each walk, four sequences are defined:

- `x_boundary`: $ \pi(n, 0) $, $ n \ge 1 $;
- `y_boundary`: $ \pi(0, n) $, $ n \ge 1 $;
- `x_marginal`: $ P(L_1 = n) = \sum_{j \ge 0} \pi(n, j) $;
- `y_marginal`: $ P(L_2 = n) = \sum_{i \ge 0} \pi(i, n) $.

For every walk of an input file, each of these sequences $ a_n $ satisfies $ a_n \sim C\, n^{\kappa} \rho^{n} $ as $ n \to \infty $, with constants $ C > 0 $, $ 0 < \rho < 1 $ and a rational number $ \kappa $.

**Program interface.** The program is the regular file `/root/qtails/tails.py`, not a symbolic link. Every entry under `/root/qtails/` must likewise be a regular file or a directory, not a symbolic link. The program is run as

```
python3 /root/qtails/tails.py INPUT.json OUTPUT.json
```

`INPUT.json` is a JSON object with the single key `"walks"`, whose value is a list of walks. Each walk is an object with exactly five keys:

- `"id"`: a string, unique within the file;
- `"interior"`, `"x_axis"`, `"y_axis"`, `"origin"`: the four laws.

Each law maps a jump, written as the string `"a,b"`, to its probability, written as a string `"p/q"` with integers $ p \ge 1 $ and $ q \ge 1 $. Jumps that are not listed have probability zero. An example input:

```json
{"walks": [{"id": "w1",
            "interior": {"-1,0": "3/10", "1,0": "1/5", "0,-1": "1/4", "0,1": "1/8", "0,0": "1/8"},
            "x_axis":   {"-1,0": "1/2", "1,0": "1/5", "0,1": "1/8", "0,0": "7/40"},
            "y_axis":   {"0,-1": "1/2", "1,0": "1/5", "0,1": "1/8", "0,0": "7/40"},
            "origin":   {"1,0": "1/5", "0,1": "1/8", "0,0": "27/40"}}]}
```

`OUTPUT.json` must be a regular file, not a symbolic link, of at most 1,000,000 bytes. It must contain one strict JSON object:

- no duplicate keys;
- no `NaN` or `Infinity`;
- no booleans or numbers where strings are required.

Its keys are exactly the walk ids of the input, in any order. Each value is an object with exactly the four keys `x_boundary`, `y_boundary`, `x_marginal` and `y_marginal`. Each of those maps to an object with exactly the two string keys `"rho"` and `"kappa"`:

```json
{"w1": {"x_boundary": {"rho": "...", "kappa": "..."},
        "y_boundary": {"rho": "...", "kappa": "..."},
        "x_marginal": {"rho": "...", "kappa": "..."},
        "y_marginal": {"rho": "...", "kappa": "..."}}}
```

`rho` is a decimal string with at least 15 significant digits, optionally in exponent notation. `kappa` is the exact value of $ \kappa $, written as an integer (`"2"`), a fraction (`"-5/3"`) or a finite decimal (`"-0.25"`).

`/root/examples.json` contains four example walks in the input format, and `/root/examples_output.json` contains the corresponding output.

**Output accuracy.** For every walk of an input file, with no exception for any walk of the additional file below, the program must report, for each of the four sequences:

- `kappa` equal to the exact $ \kappa $;
- `rho` within relative error $ 10^{-9} $ of the exact $ \rho $.

**Additional inputs.** The program must process, in a single run, one file of 31 additional walks that you are not given. The program must accept the input format above, with previously unseen ids in random order. Unlike the examples, these walks include:

- walks of classical two-node queueing networks at natural rational rates: Jackson networks with feedback, tandem networks, coupled processors, and parallel queues with single and paired arrivals;
- walks whose rational parameters lie exactly on the boundary between two asymptotic regimes, so that two of the singular points that determine the tails coincide exactly;
- heavy-traffic walks, with $ \rho $ up to $ 0.98 $;
- near-coincidences: in 10 walks, two of those singular points lie within a relative distance between $ 3 \times 10^{-5} $ and $ 10^{-3} $ of each other;
- 12 walks whose interior mean has one positive component.

Their probabilities are fractions with denominators below $ 10^{16} $. Every interior law gives positive probability to between 4 and 9 jumps. Every exact $ \rho $ lies between $ 0.1875 $ and $ 0.98 $.

**Running conditions.** The program must work in a separate container without network access. That container has the same operating system, Python and Python packages as this environment had at the start; nothing you install now carries over.

- Before the run, every `*.pyc` file and `__pycache__` directory under `/root/qtails/` is deleted.
- The program runs as an unprivileged user, with 4 CPUs, 8 GB of memory and 4 GB of disk.
- Each run of the program starts in a fresh, empty working directory, which is also `HOME` and `TMPDIR`; nothing in it persists between runs.
- The run on the 31 additional walks must finish within 1800 seconds of wall-clock time and exit with status 0. At that limit, and when the program exits, all of its processes are killed.

Correctness of the output file is binary: the file is correct only when every walk meets the accuracy requirements above, and a file with any incorrect walk is incorrect as a whole.

You have 18000 seconds to complete this task. Do not cheat by using online solutions or hints specific to this task.
