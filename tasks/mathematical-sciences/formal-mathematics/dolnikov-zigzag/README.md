<!-- Managed header -- regenerate with tools/task-readme/generate.py. Edit task.toml, not these lines. Content below END MANAGED HEADER is authored. -->

# dolnikov-zigzag

Formalize the zig-zag theorem for Kneser graphs of arbitrary set systems under the alternation-number bound (Ky Fan's lemma) as an axiom-free Lean 4 / Mathlib proof, and use it to determine the chromatic number of a given set system.

| | |
|---|---|
| **Author** | Salim Abdlselam (Independent Researcher) — salim.a@turing.com |
| **Profile** | https://uk.linkedin.com/in/salim-abdul-8119a013b |
| **Domain** | mathematical-sciences / formal-mathematics / topological-combinatorics |
| **Tags** | `lean4` `mathlib` `kneser-graph` `zig-zag-theorem` `alternation-number` `ky-fan-lemma` `borsuk-ulam` `topological-combinatorics` `formal-verification` |
| **Expert time estimate** | 50 hours |
| **Agent budget** | 5 hours |
| **Resources** | 4 CPUs · 8 GB RAM |

See [instruction.md](instruction.md) for the task as the agent receives it, and [task.toml](task.toml) for the full environment and verifier configuration.

## Author's relevant experience

Contractor authoring Terminal-Bench-Science mathematics tasks; background in formal mathematics and combinatorics to be completed by the contributor.

<!-- END MANAGED HEADER -->

## Difficulty

The task asks for a complete, kernel-checked Lean 4 proof of the zig-zag theorem for Kneser graphs of arbitrary set systems under the **alternation-number** bound, and its use on a concrete set system.

- **The general theorem.** Take a set system `F` on `[n]` and a proper colouring `c` of its Kneser graph with arbitrarily many colours. Suppose every sign vector whose positive and negative parts contain no member of `F` alternates at most `n − t` times. Then `F` contains `t` sets with strictly increasing colours such that sets with indices of opposite parity are disjoint.
- **Where it comes from.** It combines the alternation-number bound of Alishahi and Hajiabolhassan (the linear-order idea behind Schrijver's theorem) with the Simonyi–Tardos zig-zag conclusion. It strictly strengthens the Dol'nikov bound `χ(KG(F)) ≥ cd₂(F)`, because the alternation bound is never weaker and often far stronger. On the family of the data part it gives 4 where Dol'nikov's defect gives 2.
- **The data part.** The agent must determine and prove the chromatic number of the Kneser graph of `/app/data/family.json`.

Every known proof rests on the Borsuk–Ulam theorem or a combinatorial equivalent of it. Mathlib contains none of Borsuk–Ulam, Tucker's lemma, Ky Fan's lemma, Sperner-type parity arguments, alternation numbers or Kneser-graph colouring bounds. To our knowledge none of these results has been formalized in any proof assistant.

A solution must:

- prove Ky Fan's parity statement about *alternating* chains of an antipodal labelling of the cross-polytope. Tucker's lemma, enough for a plain chromatic bound, does not give the zig-zag;
- find a labelling that works under the alternation hypothesis. The labelling that suffices under Dol'nikov's defect bound gives a small sign vector `±|x|`, and it is not free of complementary pairs here (see "Where the environment drives the science" below). The small labels have to be built from the alternation number itself, signed by the first nonzero entry;
- prove the key combinatorial fact this needs. If `x ⪯ y` then `alt(x) ≤ alt(y)`, and if the first nonzero signs differ the inequality is strict. In the oracle this is a lemma about block counts of sublists;
- extract the zig-zag from an alternating chain, with the correct parity and disjointness bookkeeping;
- compute the data family's alternation bound and chromatic number, and turn them into kernel-checkable certificates.

This is the work of researchers who formalize combinatorics in Lean/Mathlib, extending the library with results it does not yet have.

### Why a 5-hour agent budget is sufficient

The expert estimate of 50 hours is for a human formalizer who must first work out the Ky Fan parity argument, the labelling and the extraction, and who types Lean at human speed. The 5-hour (18,000 s) agent budget is exactly one tenth of that. It is enough because the mathematics is classical and agents know the Freund–Todd path-following proof of Tucker's lemma and Matoušek's labelling, and generate Lean at a rate of thousands of lines per hour; the reference proof is about 1,600 lines. What an agent still needs is the modification to alternating chains, the alternation labelling and its monotonicity lemma, and a rebuild of the project takes about two minutes, so many compile-and-repair iterations fit in the budget.

## Reference solution

The oracle is `solution/solve.py`, run by `solve.sh`.

1. It reads the starter project and checks that `Defs.lean` defines `blockCount`, `signSeq` and `alternation` as expected.
2. It parses the statement of `alternation_zigzag` and its binder names from `Goal.lean`, and checks that this statement is the one proved by the Lean proof library in `solution/proof_library/`.
3. It installs the library modules and derives the proof of the goal from the parsed binders.
4. For the data part it reads `/app/data/family.json` and computes by search the alternation bound `t = n − max alt` (4), the chromatic number (4) and a proper 4-colouring. It checks the family against `Defs.lean` and generates the Lean proof of `FamilyChromaticNumber 4`. The colouring and the alternation bound are checked by `decide`, and the zig-zag theorem gives the lower bound.
5. Finally it runs `lake build Zigzag` and audits the axioms of both theorems with `#print axioms`.

The library is about 1,600 lines, with no `sorry` and axioms exactly `propext`, `Classical.choice` and `Quot.sound`. In a formal-proof task the solver's "computation" is elaboration and kernel checking of this source, so the library plays the role that solver code plays in a numerical task. It proves the theorem in four parts.

- **Ky Fan's lemma** (`FanLabels.lean`, `FanTucker.lean`, `FanStep.lean`).
  - Sign vectors are encoded as finite sets of pairs `(i, ±)` with no opposite pair, so that `⪯` is `⊆`.
  - Maximal chains of the face poset of the cross-polytope boundary are encoded as injective sequences of signed coordinates. The label of a chain at level `j` is the label of its prefix.
  - The lemma: for every antipodal labelling `λ` with no complementary pair, the number of level-`d` chains whose label sequence is positively alternating (with pairwise distinct absolute values) is odd for every `d ≤ n`. The proof is by induction on `d` through a swap-and-extend involution/handshake argument.
- **Alternation numbers** (`Alt.lean`).
  - `blockCount` is monotone along sublists, and strictly increases when the first entry changes.
  - Hence for valid signed sets `x ⊆ y`, `alt(x) ≤ alt(y)`, and equality forces the same first nonzero sign. Alternation is invariant under negation.
- **Labelling** (`Lab.lean`). Let `s = n − t`.
  - If the positive and negative parts of a signed set `x` contain no member of `F`, then `x` gets `±alt(x)`, signed by its first nonzero entry.
  - Otherwise `x` gets `±(s + 1 + c*(x))`, where `c*(x)` is the largest colour of a member of `F` inside either part, and the sign is that of the part where the maximum is attained.
  - Properness of `c` gives antipodality. The hypothesis `ht` gives `alt(x) ≤ s` for small `x`. The monotonicity lemma then rules out complementary pairs between small vectors.
- **Extraction** (`Extract.lean`, `Main.lean`).
  - In an alternating chain with distinct absolute values, the `t` indices carrying the largest absolute values have labels `≥ s + 1`, increasing absolute values and alternating signs.
  - These are big, so each carries a member `A_i` of `F` inside its positive or negative part, with `c(A_i) = |label| − s − 1`.
  - Nestedness of chain prefixes and opposite signs give disjointness for indices of opposite parity.

### Where the environment drives the science

The task has a data part whose answer is not given. `/app/data/family.json` is a set system of 17 subsets of a 7-element set. The agent must determine the chromatic number `k` of its Kneser graph and prove `FamilyChromaticNumber k`. The verifier computes the true value itself, and only the true value can be proved. Getting there is driven by computation on the data:

- **Upper bound:** the agent searches for a proper colouring of the 17-vertex Kneser graph with as few colours as possible (4 suffice).
- **Lower bound:** the obvious certificates are too weak.
  - The family contains three pairwise disjoint sets, so a triangle certifies only 3.
  - Dol'nikov's 2-colourability defect is only 2.
  - Brute force over the colourings is not feasible in Lean.

  The agent has to compute the family's alternation bound, `n` minus the largest alternation of a sign vector with no member in either part. That bound is 4, and the general theorem then gives the lower bound. A solver that proved only the defect version of the theorem cannot finish this part.
- **The general proof needs exploration too:** natural labellings fail under the alternation hypothesis. `solution/explore_labellings.py` (an exploration aid, not used by `solve.sh`) brute-forces the reduction on random small set systems with `t` equal to their alternation bound. On 156 instances (seed 1), the alternation labelling never produces a complementary pair. The cardinality labelling `±|x|`, which suffices under the defect bound, fails on 9 of them.

### Why the oracle ships Lean source

This is a formal-proof task. The deliverable is Lean source, and its correctness comes from Lean elaborating it and the kernel checking it. No general procedure derives a ~1,400-line proof of a new theorem from its statement, so any correct oracle for a proof task must supply proof source, just as the oracle of a programming task supplies program source. The proof library in `solution/proof_library/` is the solver code. It is kept in separate files called from `solve.py`, and every line of it is re-checked by the kernel on each run.

`solve.py` uses the task inputs and fails rather than guess. It checks `Defs.lean`, parses the goal and its binder names from the starter `Goal.lean`, and refuses to continue if the statement differs from the one the library proves. It then writes the proof of the goal, rebuilds the project from source and audits the axioms of the result. The verifier never imports the oracle. It independently pins the statement against `ZigzagSpec.Statement`, derives a held-out instance, audits axioms and re-runs the kernel check.

## Environment

The image holds Lean 4.34.1 and the Mathlib v4.34.1 sources. To fit a 10 GB sandbox, only the Mathlib modules imported by `Zigzag/Defs.lean` are prebuilt from Mathlib's cache, together with all of their dependencies. That is about 1,900 modules (finite sets, set families, graph colourings, signs, `ZMod`, permutations, big operators, order, common tactics), about 1.3 GB instead of 6.4 GB. The reference solution needs nothing beyond them. The instruction tells the agent which modules are prebuilt and that any other import is compiled from source.

## Verification

`tests/test_outputs.py` runs six deterministic pytest checks in a separate no-network verifier image that has Lean 4.34.1 and the same prebuilt part of Mathlib v4.34.1 baked in. The reward is 1 iff all of them pass. The submission is the directory `/app/Zigzag/`.

1. **Artifact contract:** `Goal.lean` exists and every submitted file is a regular `.lean` file.
2. **Source scan (grader integrity only):** with comments stripped, no submitted file contains a construct that would run submitted code while the verifier compiles or loads it, such as `#eval`, `run_cmd`, macros, elaborators, simprocs, initializers, `native_decide`, `implemented_by`/`extern`, metaprogramming monads or `IO`, and the options that switch off kernel checking (`set_option debug.*`, `skipKernelTC`). Such code runs as root in the grading container and could rewrite verifier files or forge reports. The scan does not restrict mathematical representation: `instance`, `notation`, `opaque` and even `axiom` declarations are allowed, because soundness is enforced by checks 3, 5 and 6.
3. **Build from source:** the verifier restores its own `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `Zigzag.lean`, `ZigzagSpec.lean` and `Zigzag/Defs.lean`, wipes `.lake/build`, and rebuilds with `lake build Zigzag ZigzagSpec`. The build must succeed with no "declaration uses sorry" warning.
4. **Statement pins, held-out instance and data answer:** `ZigzagSpec.Statement` is the goal statement elaborated in a verifier-owned module that imports only `Zigzag.Defs` and Mathlib, never the submission. The verifier-owned `Check.lean` requires `@Zigzag.alternation_zigzag : ZigzagSpec.Statement`, so instances or notation declared in the submission cannot change the meaning of the statement (cheat 13 below shows this). It then derives from the submitted theorem a held-out instance that the submission never sees: every proper colouring of the Petersen graph `KG(5,2)` contains a path `A – B – C` with strictly increasing colours. The verifier proves by `decide` that `t = 3` is a valid alternation bound for the 2-subsets of `[5]`: a sign vector with no such pair inside either part alternates at most twice. Finally `Check.lean` requires `Zigzag.family_chromatic_number : Zigzag.FamilyChromaticNumber k`, where `k` is the verifier's own reference value. `test_outputs.py` computes it from its copy of `data/family.json` (checked against `family` in `Defs.lean`) by a method independent of the oracle's backtracking colouring search. It lists all maximal independent sets of the Kneser graph with Bron–Kerbosch (22 of them) and takes the least number of them that cover all 17 vertices, which is 4. The value is inserted as `Nat.succ` applications so that submitted instances cannot reinterpret it.
5. **Axiom audit:** the kernel environment is traversed from both theorems, the pins and the held-out instance, and the axioms reached must be a subset of `{propext, Classical.choice, Quot.sound}`.
6. **Kernel re-check:** every submitted theorem, definition and `opaque` declaration reachable from those roots is re-added to the environment with kernel type checking enabled (via `Environment.addDeclCore`). Inductive types are kernel-checked when the build adds them, which is sound because the kernel-bypass options are banned by the source scan.

All Lean invocations of checks 3–6 share one 1,200-second budget, as the instruction states.

Local evidence (from the offline verifier image; the cheat submissions and logs are kept with the author's working files, not in the task package): the oracle scores 1 in five out of five runs (125–135 s each), the unmodified starter (`nop`) scores 0, and all thirteen adversarial submissions score 0. They are: a `sorry`, an added `axiom`, a `sorryAx` term, a weakened conclusion, an extra hypothesis (proved), an instance that shadows `%`, `native_decide`, `skipKernelTC`, a macro-hidden `sorry`, a `run_cmd`, a tampered `Defs.lean` (restored by the verifier), a stray non-Lean file, and a sorry-free, axiom-clean proof that trivialises the statement by shadowing `<` and `%` on ℕ with high-priority instances (rejected by the independent statement pin).
