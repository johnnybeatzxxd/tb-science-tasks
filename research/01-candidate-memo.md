# TB-Science maths task — candidate research memo (round 1)

Date: 2026-10-07. Status: for review; nothing is packaged yet.

## 1. What the canonical rules add to the handoff

Source: `harbor-framework/terminal-bench-science` at commit `8ef49c8` (2026-10-06):
`CONTRIBUTING.md`, `rubrics/task-implementation.toml` (39 criteria), `rubrics/task-proposal.md`.

- **Difficulty target.** The benchmark aims for tasks that frontier models solve only 10–20% of the time.
- **Turing gate.** The task must break at least one model in one attempt. The models are GPT-6 Sol at max effort and Claude Opus 5.5 at low effort, both run through the Terminus-2 agent.
- **No hunting for model blind spots.** Generating many candidates and keeping whichever ones current models happen to fail is explicitly discouraged. So are trick questions, and instructions that "suggest the wrong answer". This rules out pure trap tasks, where the wording invites a mistake.
- **Thresholds stay hidden.** Every metric that gates the result must be named, but its numeric cutoff may be withheld. Withholding it is preferred when it would only tell the agent where to stop.
- **A tolerance used to separate correct methods from wrong ones needs real evidence.** It must be measured on at least one correct implementation that is structurally independent of the reference, and the gap between correct and wrong methods must be reported.
- **`authoring/` is canonical.** `hint.md` belongs there. Per the user's decision, we will include `authoring/`.
- **Required `task.toml` fields the old task may have missed:** `author_organization`, `relevant_experience` and `conflicts_of_interest`.
  - Data-vendor rule: an expert engaged by a vendor uses an academic affiliation or "Independent Researcher", and discloses the engagement in `conflicts_of_interest`.

## 2. Why the old task failed (evidence from the eval export)

- Both models passed in about 8 minutes and about $0.30 each, using about 13 steps out of an 18,000-second budget. Opus did this at **low** effort.
- The instruction gave the full model family, the exact sparsity counts and the noise level. That made the task an ordinary least-squares fit with a built-in stopping signal: residuals reaching the stated noise level told the agent it was done.

**Design lesson:**
- Any task where the agent can check its own answer, and the remaining work is routine numerics, will fall.
- A hard task either (a) needs a large amount of genuine expert work, or (b) has a natural approach that converges confidently to a wrong answer the agent cannot detect.
- (b) must arise from the science itself, never from misleading wording.

## 3. Candidates (ranked)

### #1 — Formalise the Kneser–Lovász theorem in Lean 4 (formal-mathematics) — RECOMMENDED

**Problem.**
- Kneser graph KG(n,k): vertices are the k-subsets of an n-element set; two are adjacent when they are disjoint.
- Lovász (1978) proved χ(KG(n,k)) = n − 2k + 2 for n ≥ 2k ≥ 2. This proof founded topological combinatorics.
- The upper bound is an easy explicit colouring.
- The lower bound needs Borsuk–Ulam, or its combinatorial form, Tucker's lemma (octahedral version: Freund–Todd 1981; Matoušek 2004).

**Gap in Mathlib (cloned 2026-10-07, toolchain v4.35.0-rc4).**
- Mathlib has none of Kneser graphs, Tucker's lemma, Borsuk–Ulam or Brouwer's fixed-point theorem.
- Web search found no Lean, Isabelle or Coq formalisation of Kneser–Lovász.
  - "Kneser" results in Isabelle and Mathlib are the unrelated additive theorem.
  - The Lovász local lemma exists only in Isabelle.

**Graded artefact.**
- The agent fills a frozen `Goal.lean`: `theorem kneser_lovasz (n k) (hk : 1 ≤ k) (hn : 2*k ≤ n) : (kneserGraph n k).chromaticNumber = n - 2*k + 2`.
- `Defs.lean` defines `kneserGraph` with Mathlib vocabulary only.

**Verifier.** The hardened Lean pattern already accepted twice in this benchmark:
- restore the frozen files;
- rebuild in an image with no network;
- pin the exact type of the theorem;
- check that the axioms used are only {propext, Classical.choice, Quot.sound};
- scan the source for `sorry`, `native_decide`, `axiom`, macros and similar escapes.

Ground truth is the Lean kernel itself, which is fully independent of our solution. There are no tolerances.

**What the agents will try, and why it fails.**
- **GPT-6 (max).** It knows Matoušek's proof. It will set up sign vectors and try to formalise octahedral Tucker. Its main risks:
  - the parity/path-following core (degree-2 graph on chains of sign vectors) is long and fiddly;
  - the antipodal labelling from a colouring needs careful Finset combinatorics;
  - the Terminus-2 keystroke harness makes iterating on Lean slow.

  A plausible full proof is 2,000–4,000 lines. Finishing inside 18,000 s in one attempt is very unlikely but not impossible. My estimate is ≤ 15%.
- **Opus (low).** It will try a short proof, hit the topological core, and run out of time or submit something incomplete. I estimate close to 0%.
- **Shortcuts.**
  - Small-n `decide` doesn't help because the statement is universally quantified over n and k.
  - `native_decide`, axioms and redefined instances are banned and checked by the verifier.
  - Changing the statement is caught by the type pin.

**Expert / oracle.**
- Matoušek's reduction: a colouring with n − 2k + 1 colours gives an antipodal labelling of {+,−,0}ⁿ∖{0} by ±{1,…,n−1} with no complementary edge.
- Combinatorial octahedral Tucker lemma (Freund–Todd parity argument) closes the proof.
- The upper bound uses the standard colouring by minimum element, capped at n − 2k + 2.
- My estimate is 2,000–3,500 Lean lines, several days of work.

**Main risks.**
1. **Oracle cost on our side.** It is large but tractable, because finite combinatorics is Lean's strongest area.
2. **Lean/Mathlib in this dev container.** The release binaries and the Mathlib cache are blocked by the network policy. Fix: allow those domains, or build from source, which takes hours.
3. **Turing resources.** Lean tasks need about 4 CPUs, 8 GB RAM, 20 GB storage and a ~30-minute build. Accepted Lean tasks use exactly this.
4. **Precedent.** Accepted formal tasks already exist: `finite-free-stam`, `onsager-ising-lean` (a 1944 theorem) and `regularized-game-proof`. So "formalise a landmark theorem missing from Mathlib" is an accepted research workflow.

### #2 — Exact flag-algebra certificate for an extremal-combinatorics density bound (operations-research / formal-adjacent)

- **Task.** Certify an upper bound on a Turán-type density with an exact rational certificate (flag types, Gram matrices). The verifier rebuilds the flag algebra and checks positive-semidefiniteness and the bound exactly.
- **Why it's hard.**
  - It needs a flag-algebra engine built from scratch: enumerating graphs up to isomorphism, products of flags, averaging.
  - It needs a large semidefinite program solved and then rounded to an exact certificate. Naive rounding fails whenever the bound is tight, and fixing that takes expertise.
- **Risks.**
  - Bodnár's FlagAlgebraToolbox (SageMath, January 2026) may automate the whole pipeline if the agent manages to install Sage.
  - The certificate format makes the specification heavy.
  - The verifier is a large program of our own.

### #3 — Defect eigenvalues in the spectral gap of a perturbed periodic operator (applied-mathematics)

- **Task.** Report all eigenvalues inside a stated gap. Truncating the domain and discretising produces spurious eigenvalues ("spectral pollution") that look fully converged.
- **Expert fix.** Pollution-free methods (second-order relative spectrum, or Floquet-matched Evans function) plus rigorous enclosures.
- **Verifier.** Count and values, against truth from two independent methods.
- **Risks.**
  - A careful agent that varies the truncation can spot non-converging eigenvalues.
  - In 1-D it is likely solvable; in 2-D it drifts towards being merely slow.

### #4 — 30+ digit Hausdorff dimension of a new continued-fraction Cantor set (applied-mathematics)

- **Task.** Generic methods give 4–8 digits. Getting further needs transfer-operator spectral methods (Jenkinson–Pollicott, Falk–Nussbaum).
- **Risks.**
  - The precision requirement reads as "arbitrary precision" under the rubric.
  - Frontier models know these methods.

### #5 — Complete solution sets of polynomial systems from applications (e.g. Kuramoto/power-flow equilibria)

- **Risk.** HomotopyContinuation.jl can be installed from the internet and solves these robustly. Rejected unless the system has structure that defeats it.

### #6 — Numerical continuation / branch completeness (handoff suggestion)

- **Risk.** Deflation and arclength continuation are well known to frontier models. Proving that an agent has found all branches needs an independent count, and the instance becomes a puzzle.

## 4. Recommendation

Build #1 (Kneser–Lovász in Lean 4). It is the only candidate where all of these hold at once:
- (a) grading is absolute and independent of our code;
- (b) the difficulty is a large amount of genuine expert mathematics, not a trap or a threshold;
- (c) there is no off-the-shelf tool or existing formalisation to copy;
- (d) it fits the accepted precedent.

Its cost lands on us, since we must write the full proof.

Keep #2 as the fallback if Turing's pipeline cannot host Lean tasks.

## 5. Plan once approved

1. **Environment.** Get Lean and Mathlib running locally at a pinned toolchain (needs network allow-list or a source build).
2. **Probe the agent before writing the oracle.** Give a blind Claude subagent the exact task with an 18,000 s budget and record how far it gets. If it solves quickly, drop the candidate before spending days on the proof.
3. **Oracle.** Write the full formal proof, file by file (sign vectors and Tucker → labelling from a colouring → lower bound → upper bound).
4. **Verifier.** Hardened verifier, cheat-attempt suite (redefined instances, `sorry` smuggling, statement edits), oracle = 1, nop = 0, offline run.
5. **Final adversarial runs.** Read the transcripts to confirm the failures are scientific.
