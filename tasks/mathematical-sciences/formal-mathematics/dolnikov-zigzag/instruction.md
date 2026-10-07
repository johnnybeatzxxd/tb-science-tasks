Prove the Dol'nikov–Simonyi–Tardos zig-zag theorem for arbitrary set systems in Lean 4 with Mathlib.

The Lean project in `/app` (Lean and Mathlib v4.34.1, already built) contains `/app/Zigzag/Defs.lean`, which defines what it means for a subset `A` of the ground set `Fin n` to be monochromatic for a 2-colouring `col : Fin n → Bool` (`Zigzag.Mono col A`: all elements of `A` get the same colour), and `/app/Zigzag/Goal.lean`, which states

```lean
theorem dolnikov_zigzag {n : ℕ} (F : Finset (Finset (Fin n))) (c : Finset (Fin n) → ℕ)
    (hc : ∀ A ∈ F, ∀ B ∈ F, Disjoint A B → c A ≠ c B) (t : ℕ)
    (ht : ∀ (D : Finset (Fin n)) (col : Fin n → Bool),
      (∀ A ∈ F, A ⊆ Dᶜ → ¬ Mono col A) → t ≤ D.card) :
    ∃ f : Fin t → Finset (Fin n), (∀ i, f i ∈ F) ∧ (∀ i j, i < j → c (f i) < c (f j)) ∧
      ∀ i j : Fin t, ((i : ℕ) + j) % 2 = 1 → Disjoint (f i) (f j)
```

with the proof replaced by `sorry`. In words: `c` is a proper colouring (with colours in `ℕ`, any number of them) of the Kneser graph of the set system `F`, and `t` is a lower bound for the 2-colourability defect of `F`; the conclusion is that `F` contains `t` sets whose colours are strictly increasing and such that any two of them with indices of opposite parity are disjoint (a "zig-zag" complete bipartite subgraph of the Kneser graph). Replace the `sorry` with a complete proof.

Keep the statement of `Zigzag.dolnikov_zigzag` exactly as given. You may add definitions, lemmas and theorems to `Goal.lean` or to new `.lean` files under `/app/Zigzag/`; files you add are compiled only if `Goal.lean` imports them, directly or transitively. Only the directory `/app/Zigzag/` is graded: the verifier restores its own copies of `/app/Zigzag/Defs.lean`, `/app/Zigzag.lean`, `/app/ZigzagSpec.lean`, `/app/lakefile.toml`, `/app/lake-manifest.json` and `/app/lean-toolchain`, deletes `/app/.lake/build`, and rebuilds with `lake build Zigzag ZigzagSpec`. The whole verification runs offline and must finish within 1200 seconds, which covers that rebuild from source and three further `lake env lean` checks (statement, axioms, kernel re-check); a submission that takes longer to compile fails.

The submission passes only if all of the following hold:

- `/app/Zigzag/` contains only regular `.lean` files, and `lake build Zigzag` succeeds with no declaration using `sorry`;
- `Zigzag.dolnikov_zigzag` has exactly the type above: it is checked against `ZigzagSpec.Statement` in `/app/ZigzagSpec.lean`, the same statement elaborated in a module that does not import your files, so instances or notation you declare cannot change its meaning;
- the theorem depends on no axioms other than `propext`, `Classical.choice` and `Quot.sound`, and every declaration it uses from `/app/Zigzag/` passes a fresh Lean kernel check;
- because the verifier compiles and loads your files, no file under `/app/Zigzag/` may contain, outside comments, a construct that runs your code at that time: the commands `#eval`, `#exit`, `run_cmd`, `run_elab`, `run_meta`, `run_tac`, `macro`, `macro_rules`, `elab`, `elab_rules`, `initialize`, `builtin_initialize`, `simproc`, `dsimproc`; `native_decide` or `decide +native`; the attributes `implemented_by`, `extern`, `init`, `builtin_init`; the identifiers `IO`, `BaseIO`, `EIO`, `unsafeBaseIO`, `unsafeIO`, `unsafeEIO`, `unsafePerformIO`, `FilePath`, `MetaM`, `TacticM`, `CoreM`, `TermElabM`, `CommandElabM`, `SimpM`, `addDecl`, `addDeclCore`, `setEnv`, `modifyEnv`, `ofReduceBool`, `trustCompiler`; or, outside `import` lines, names under `Lean.Meta`, `Lean.Elab`, `Lean.Tactic`, `Lean.Compiler`, `Lean.Environment`, `Mathlib.Meta`, `Mathlib.Elab`, `Mathlib.Tactic`, `Mathlib.Compiler` or `Mathlib.Environment`. Everything else is allowed (for example `instance`, `notation`, `opaque` or `axiom` declarations); soundness is enforced by the build, the axiom condition and the kernel check above.

You have 18000 seconds to complete this task. Do not cheat by using online solutions or hints specific to this task.
