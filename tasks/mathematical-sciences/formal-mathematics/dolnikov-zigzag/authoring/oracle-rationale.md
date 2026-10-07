# Why the oracle ships Lean source

This is a formal-proof task. The deliverable is Lean source, and the "computation" that makes it correct is Lean's elaboration and kernel checking of that source. A proof of a new theorem cannot be computed from the statement by a general procedure: no automated prover produces this ~1,400-line argument. Any correct oracle for a proof task therefore has to supply proof source, just as the oracle for a programming task supplies program source. Copying source into the build tree is how a proof is installed, not a stored answer key.

What `solution/solve.py` does with the task inputs:

1. It reads `/app/Zigzag/Defs.lean` and checks that `Mono` is defined as the proof library assumes.
2. It parses `/app/Zigzag/Goal.lean`, extracts the statement of `dolnikov_zigzag` and its top-level binder names, and checks that the statement is the one proved by `zigzag_main` in the library. It refuses to proceed otherwise.
3. It installs the library modules, writes the proof of the goal from the parsed binders (`exact zigzag_main F c hc t ht`), and runs `lake build Zigzag`. Elaboration and the kernel check the whole argument from scratch, and the script fails if the build fails or any declaration uses `sorry`.
4. It runs `#print axioms` on the result and fails unless the axioms are within `propext`, `Classical.choice` and `Quot.sound`.

The library (`solution/proof_library/`) is the solver code, kept in separate files as the trainer guide requires ("put real code in separate files and call them by absolute path; do not paste large scripts inline"). It contains a real argument with four parts:

- Ky Fan's parity lemma for alternating chains of the cross-polytope (`FanLabels`, `FanTucker`, `FanStep`).
- The antipodal labelling built from the colouring and the defect bound (`Lab`).
- The extraction of the zig-zag from an alternating chain (`Extract`).
- The final assembly (`Main`).

None of it is a stored output. Every line is re-checked by the Lean kernel each time the oracle runs, and the verifier independently re-checks the result (statement pin against a separately elaborated statement, held-out Petersen-graph instance, axiom audit, kernel re-check).
