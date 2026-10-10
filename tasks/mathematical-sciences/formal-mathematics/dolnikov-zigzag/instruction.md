Prove the zig-zag theorem for Kneser graphs of arbitrary set systems under the alternation-number bound, in Lean 4 with Mathlib, and use it to determine the chromatic number of the Kneser graph of a given set system.

The Lean project in `/app` uses Lean and Mathlib v4.34.1. The Mathlib modules imported by `/app/Zigzag/Defs.lean` (finite sets and fintypes, set families and graph colourings, signs, `ZMod`, permutations, big operators, order, and the common tactics) are prebuilt together with all of their dependencies; any other Mathlib module you import is compiled from source by Lake, also during verification. The project contains `/app/Zigzag/Defs.lean`, which defines the alternation number of a sign vector `x : Fin n → SignType` (`Zigzag.alternation x`: the number of maximal blocks of equal signs among the nonzero entries of `x`, read in increasing order of the index, so `+ 0 − − +` has alternation number 3 and the zero vector 0), and `/app/Zigzag/Goal.lean`, which states

```lean
theorem alternation_zigzag {n : ℕ} (F : Finset (Finset (Fin n))) (c : Finset (Fin n) → ℕ)
    (hc : ∀ A ∈ F, ∀ B ∈ F, Disjoint A B → c A ≠ c B) (t : ℕ)
    (ht : ∀ x : Fin n → SignType,
      (∀ A ∈ F, ¬ (∀ i ∈ A, x i = 1) ∧ ¬ (∀ i ∈ A, x i = -1)) → alternation x + t ≤ n) :
    ∃ f : Fin t → Finset (Fin n), (∀ i, f i ∈ F) ∧ (∀ i j, i < j → c (f i) < c (f j)) ∧
      ∀ i j : Fin t, ((i : ℕ) + j) % 2 = 1 → Disjoint (f i) (f j)
```

with the proof replaced by `sorry`. In words: `c` is a proper colouring (with colours in `ℕ`, any number of them) of the Kneser graph of the set system `F`, and every sign vector whose positive part and whose negative part both contain no member of `F` has alternation number at most `n − t`; the conclusion is that `F` contains `t` sets whose colours are strictly increasing and such that any two of them with indices of opposite parity are disjoint (a "zig-zag" complete bipartite subgraph of the Kneser graph). Replace the `sorry` with a complete proof.

Then apply it to data. `/app/data/family.json` describes a set system on the ground set $ \{0, \dots, 6\} $ (key `sets`); the same system is defined in `Defs.lean` as `Zigzag.family`, together with its Kneser graph `Zigzag.kneserGraphOf family` (two members adjacent iff disjoint) and the predicate `Zigzag.FamilyChromaticNumber k`, which says that this graph has chromatic number `k`. Determine the chromatic number of this graph and prove it: add, in namespace `Zigzag` in `Goal.lean` or in a file it imports, a theorem

```lean
theorem family_chromatic_number : FamilyChromaticNumber k
```

where `k` is the numeral you found. Only the true value can be proved, and the verifier checks it against its own value.

Keep the statement of `Zigzag.alternation_zigzag` exactly as given. You may add definitions, lemmas and theorems to `Goal.lean` or to new `.lean` files under `/app/Zigzag/`; files you add are compiled only if `Goal.lean` imports them, directly or transitively. Only the directory `/app/Zigzag/` is graded: the verifier restores its own copies of `/app/Zigzag/Defs.lean`, `/app/Zigzag.lean`, `/app/ZigzagSpec.lean`, `/app/lakefile.toml`, `/app/lake-manifest.json` and `/app/lean-toolchain`, deletes `/app/.lake/build`, and rebuilds with `lake build Zigzag ZigzagSpec`. The whole verification runs offline and must finish within 1200 seconds, which covers that rebuild from source and three further `lake env lean` checks (statement, axioms, kernel re-check); a submission that takes longer to compile fails.

The submission passes only if all of the following hold:

- `/app/Zigzag/` contains only regular `.lean` files, and `lake build Zigzag` succeeds with no declaration using `sorry`;
- `Zigzag.family_chromatic_number` exists and has type `Zigzag.FamilyChromaticNumber k` for the true chromatic number `k` of `Zigzag.kneserGraphOf Zigzag.family`;
- `Zigzag.alternation_zigzag` has exactly the type above: it is checked against `ZigzagSpec.Statement` in `/app/ZigzagSpec.lean`, the same statement elaborated in a module that does not import your files, so instances or notation you declare cannot change its meaning;
- both theorems depend on no axioms other than `propext`, `Classical.choice` and `Quot.sound`, and every theorem, definition and `opaque` declaration they use from `/app/Zigzag/` passes a fresh Lean kernel check (inductive types are checked by the kernel when your project is built). No other kind of declaration is restricted;
- because the verifier compiles and loads your files, no file under `/app/Zigzag/` may contain, outside comments, a construct that runs your code at that time or bypasses the kernel: the commands `#eval`, `#exit`, `run_cmd`, `run_elab`, `run_meta`, `run_tac`, `macro`, `macro_rules`, `elab`, `elab_rules`, `initialize`, `builtin_initialize`, `simproc`, `dsimproc`; `native_decide` or `decide +native`; `set_option debug.*` and `skipKernelTC` (they switch off kernel checking); the attributes `implemented_by`, `extern`, `init`, `builtin_init`; the identifiers `IO`, `BaseIO`, `EIO`, `unsafeBaseIO`, `unsafeIO`, `unsafeEIO`, `unsafePerformIO`, `FilePath`, `MetaM`, `TacticM`, `CoreM`, `TermElabM`, `CommandElabM`, `SimpM`, `addDecl`, `addDeclCore`, `setEnv`, `modifyEnv`, `ofReduceBool`, `trustCompiler`; or, outside `import` lines, names under `Lean.Meta`, `Lean.Elab`, `Lean.Tactic`, `Lean.Compiler`, `Lean.Environment`, `Mathlib.Meta`, `Mathlib.Elab`, `Mathlib.Tactic`, `Mathlib.Compiler` or `Mathlib.Environment`. Everything else is allowed (for example `instance`, `notation`, `opaque` or `axiom` declarations); soundness is enforced by the build, the axiom condition and the kernel check above.

You have 18000 seconds to complete this task. Do not cheat by using online solutions or hints specific to this task.
