<!-- Managed header -- regenerate with tools/task-readme/generate.py. Edit task.toml, not these lines. Content below END MANAGED HEADER is authored. -->

# dolnikov-zigzag

Formalize the Dol'nikov–Simonyi–Tardos zig-zag theorem (Ky Fan's lemma for Kneser graphs of arbitrary set systems) as an axiom-free Lean 4 / Mathlib proof.

| | |
|---|---|
| **Author** | Salim Abdlselam (Independent Researcher) — salim.a@turing.com |
| **Profile** | https://uk.linkedin.com/in/salim-abdul-8119a013b |
| **Domain** | mathematical-sciences / formal-mathematics / topological-combinatorics |
| **Tags** | `lean4` `mathlib` `kneser-graph` `zig-zag-theorem` `ky-fan-lemma` `borsuk-ulam` `topological-combinatorics` `formal-verification` |
| **Expert time estimate** | 50 hours |
| **Agent budget** | 5 hours |
| **Resources** | 4 CPUs · 8 GB RAM |

See [instruction.md](instruction.md) for the task as the agent receives it, and [task.toml](task.toml) for the full environment and verifier configuration.

## Author's relevant experience

Contractor authoring Terminal-Bench-Science mathematics tasks; background in formal mathematics and combinatorics to be completed by the contributor.

<!-- END MANAGED HEADER -->

## Difficulty

The task asks for a complete, kernel-checked Lean 4 proof of the zig-zag theorem of Dol'nikov, Simonyi and Tardos for Kneser graphs of arbitrary set systems. Given a set system `F` on `[n]`, a proper colouring `c` of its Kneser graph with arbitrarily many colours, and a lower bound `t` for the 2-colourability defect of `F` (Dol'nikov's `cd₂`), it asserts that `F` contains `t` sets with strictly increasing colours such that sets with indices of opposite parity are disjoint. This is a strict strengthening of the Kneser–Lovász/Dol'nikov bound `χ(KG(F)) ≥ cd₂(F)`: the colouring is not assumed to use few colours, and the conclusion exhibits a complete bipartite subgraph with a rainbow zig-zag. The theorem is a standard application of Ky Fan's 1952 combinatorial lemma on alternating chains of antipodal labellings of the cross-polytope, and every known proof rests on the Borsuk–Ulam theorem or on a combinatorial equivalent of it. Mathlib contains none of Borsuk–Ulam, Tucker's lemma, Ky Fan's lemma, Sperner-type parity arguments or Kneser-graph colouring bounds. To our knowledge there is no formalization of Ky Fan's lemma or of the zig-zag theorem in any proof assistant.

Tucker's lemma, which is enough for the plain chromatic-number bound, is not enough here: a solution has to prove a parity statement about *alternating* chains, which is strictly more delicate than the sign-vector parity argument for Tucker. It also has to find the right antipodal labelling, which for a general set system with unbounded colour range is a non-obvious modification of Matoušek's labelling, and extract `t` sets with the required parity pattern from an alternating chain. Concretely a solution must:

- encode sign vectors and their order, and reason about maximal chains of the face poset of the cross-polytope;
- set up a counting argument (a graph on partially alternating chains, whose degree counts are established case by case) that proves Ky Fan's parity statement at every level `d ≤ n`, with off-by-one pitfalls in levels and label ranges;
- build the labelling `λ` and prove that it is antipodal and has no complementary pair `x ⊆ y` with `λ(x) = -λ(y)`;
- read the zig-zag off the `t` largest labels of an alternating chain, with the correct parity and disjointness bookkeeping.

There is no data: the object being produced is a formal proof, checked by the Lean kernel. This is the work of researchers who formalize combinatorics in Lean/Mathlib, extending the library with results it does not yet have.

### Why a 5-hour agent budget is sufficient

The expert estimate of 50 hours is for a human formalizer who must first work out the Ky Fan parity argument, the labelling and the extraction, and who types Lean at human speed. The 5-hour (18,000 s) agent budget is exactly one tenth of that. It is enough because the mathematics is classical and agents know the Freund–Todd path-following proof of Tucker's lemma and Matoušek's labelling, and generate Lean at a rate of thousands of lines per hour; the reference proof is about 1,400 lines. What an agent still needs is the modification to alternating chains and the right labelling, and a rebuild of the project takes about two minutes, so many compile-and-repair iterations fit in the budget.

## Reference solution

The oracle is `solution/solve.py` (run by `solve.sh`). It reads the starter project and checks that `Defs.lean` defines `Mono` as expected. It then parses the statement of `dolnikov_zigzag` and its binder names from `Goal.lean`, and checks that this statement is the one proved by the Lean proof library in `solution/proof_library/`. It installs the library modules, derives the proof of the goal from the parsed binders, runs `lake build Zigzag`, and audits the axioms of the result with `#print axioms`. The library is about 1,400 lines, with no `sorry` and axioms exactly `propext`, `Classical.choice` and `Quot.sound`. In a formal-proof task the solver's "computation" is elaboration and kernel checking of this source, so the library plays the role that solver code plays in a numerical task. It proves the theorem as follows.

- **Ky Fan's lemma** (`FanLabels.lean`, `FanTucker.lean`, `FanStep.lean`): sign vectors are encoded as finite sets of pairs `(i, ±)` with no opposite pair, so that `⪯` is `⊆`. Maximal chains of the face poset of the cross-polytope boundary are encoded as injective sequences of signed coordinates; the label of a chain at level `j` is the label of its prefix. For every antipodal labelling `λ` with no complementary pair, the number of level-`d` chains whose label sequence is positively alternating (with pairwise distinct absolute values) is odd for every `d ≤ n`, by induction on `d` through a swap-and-extend involution/handshake argument.
- **Labelling** (`Lab.lean`): with `s = n - t`, a signed set `x` whose positive and negative parts contain no member of `F` gets `±|x|` (sign of its first coordinate); otherwise it gets `±(s + 1 + c*(x))`, where `c*(x)` is the largest colour of a member of `F` inside either part and the sign is that of the part where the maximum is attained. Properness of `c` gives antipodality, and the defect hypothesis `ht` bounds the size of small sets by `s`, which rules out complementary pairs.
- **Extraction** (`Extract.lean`, `Main.lean`): in an alternating chain with distinct absolute values the `t` indices carrying the largest absolute values have labels `≥ s + 1`, increasing absolute values and alternating signs. They are big, so each carries a member `A_i` of `F` inside its positive or negative part, with `c(A_i) = |label| - s - 1`. Nestedness of chain prefixes and opposite signs give disjointness for indices of opposite parity.

### Why the oracle ships Lean source

This is a formal-proof task. The deliverable is Lean source, and its correctness comes from Lean elaborating it and the kernel checking it. No general procedure derives a ~1,400-line proof of a new theorem from its statement, so any correct oracle for a proof task must supply proof source, just as the oracle of a programming task supplies program source. The proof library in `solution/proof_library/` is the solver code. It is kept in separate files called from `solve.py`, and every line of it is re-checked by the kernel on each run.

`solve.py` uses the task inputs and fails rather than guess. It checks `Defs.lean`, parses the goal and its binder names from the starter `Goal.lean`, and refuses to continue if the statement differs from the one the library proves. It then writes the proof of the goal, rebuilds the project from source and audits the axioms of the result. The verifier never imports the oracle. It independently pins the statement against `ZigzagSpec.Statement`, derives a held-out instance, audits axioms and re-runs the kernel check.

## Environment

The image holds Lean 4.34.1 and the Mathlib v4.34.1 sources. To fit a 10 GB sandbox, only the Mathlib modules imported by `Zigzag/Defs.lean` are prebuilt from Mathlib's cache, together with all of their dependencies. That is about 1,900 modules (finite sets, set families, graph colourings, `ZMod`, permutations, big operators, order, common tactics), about 1.3 GB instead of 6.4 GB. The reference solution needs nothing beyond them. The instruction tells the agent which modules are prebuilt and that any other import is compiled from source.

## Verification

`tests/test_outputs.py` runs six deterministic pytest checks in a separate no-network verifier image that has Lean 4.34.1 and the same prebuilt part of Mathlib v4.34.1 baked in. The reward is 1 iff all of them pass. The submission is the directory `/app/Zigzag/`.

1. **Artifact contract:** `Goal.lean` exists and every submitted file is a regular `.lean` file.
2. **Source scan (grader integrity only):** with comments stripped, no submitted file contains a construct that would run submitted code while the verifier compiles or loads it, such as `#eval`, `run_cmd`, macros, elaborators, simprocs, initializers, `native_decide`, `implemented_by`/`extern`, metaprogramming monads or `IO`. Such code runs as root in the grading container and could rewrite verifier files or forge reports. The scan does not restrict mathematical representation: `instance`, `notation`, `opaque` and even `axiom` declarations are allowed, because soundness is enforced by checks 3, 5 and 6.
3. **Build from source:** the verifier restores its own `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `Zigzag.lean`, `ZigzagSpec.lean` and `Zigzag/Defs.lean`, wipes `.lake/build`, and rebuilds with `lake build Zigzag ZigzagSpec`. The build must succeed with no "declaration uses sorry" warning.
4. **Statement pin and held-out instance:** `ZigzagSpec.Statement` is the goal statement elaborated in a verifier-owned module that imports only `Zigzag.Defs` and Mathlib, never the submission. The verifier-owned `Check.lean` requires `@Zigzag.dolnikov_zigzag : ZigzagSpec.Statement`, so instances or notation declared in the submission cannot change the meaning of the statement (cheat 13 below shows this). It then derives from the submitted theorem a held-out instance that the submission never sees: every proper colouring of the Petersen graph `KG(5,2)` contains a path `A – B – C` with strictly increasing colours. The verifier proves by `decide` that `t = 3` is a valid defect bound for the 2-subsets of `[5]`.
5. **Axiom audit:** the kernel environment is traversed from the theorem, the pin and the held-out instance, and the axioms reached must be a subset of `{propext, Classical.choice, Quot.sound}`.
6. **Kernel re-check:** every submitted definition and theorem reachable from those roots is re-added to the environment with kernel type checking enabled (via `Environment.addDeclCore`).

Local evidence (from the offline verifier image; the cheat submissions and logs are kept with the author's working files, not in the task package): the oracle scores 1 in five out of five runs (59–66 s each), the unmodified starter (`nop`) scores 0, and all thirteen adversarial submissions score 0. They are: a `sorry`, an added `axiom`, a `sorryAx` term, a weakened conclusion, an extra hypothesis (proved), an instance that shadows `%`, `native_decide`, `skipKernelTC`, a macro-hidden `sorry`, a `run_cmd`, a tampered `Defs.lean` (restored by the verifier), a stray non-Lean file, and a sorry-free, axiom-clean proof that trivialises the statement by shadowing `<` and `%` on ℕ with high-priority instances (rejected by the independent statement pin).
