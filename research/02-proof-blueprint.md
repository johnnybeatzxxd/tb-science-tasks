# Kneser–Lovász: formalisation blueprint (author-side)

**Target.** For `1 ≤ k` and `2k ≤ n`, `χ(KG(n,k)) = n − 2k + 2`.

- `KG(n,k)` is the graph on the k-subsets of `Fin n`; two subsets are adjacent iff they are disjoint.

## A. Upper bound

**Colouring.** `c(S) = min(min S, n − 2k + 1)`, with values in `Fin (n − 2k + 2)`.

**Why it is proper.** Suppose S and T are adjacent (disjoint) with the same colour j.
- If `j < n−2k+1`: then `min S = j = min T`, so j lies in both sets, contradicting disjointness.
- If `j = n−2k+1`: then `S, T ⊆ {n−2k+1, …, n−1}`, a set of 2k−1 elements. Two disjoint k-subsets cannot fit in it.

## B. Sign vectors

**Basic objects.**
- `SV n := Fin n → SignType`.
- Order: `x ⪯ y :⇔ ∀ i, x i ≠ 0 → y i = x i`.
- Support: `supp x`, the coordinates where `x i ≠ 0`; its size is the *level* of x.
- Signed set: `S(x) := {(x i : ℤ) * (i+1) | i ∈ supp x} ⊆ ℤ∖{0}`. It is injective in x and monotone in `⪯`.

**Facts.**
- F1. If `x ⪯ y` and `|supp x| = |supp y|`, then `x = y`.
- F2. In a chain, levels are pairwise distinct.
- F2'. If v is comparable to every element of a chain σ and `level v = level(w)` for some `w ∈ σ`, then `v = w`.
- F3. If `x ⪯ y` and `|supp y| = |supp x| + 2`, then there are exactly 2 elements v with `x ⪯ v ⪯ y` and `|supp v| = |supp x| + 1`.
- F4. Let `S(z) ∌ ℓ`, `0 < |ℓ| ≤ n`, and suppose `−ℓ ∉ S(z)`. Then there is exactly one v with `S(v) = S(z) ∪ {ℓ}`, and it satisfies `z ⪯ v`.

## C. Octahedral Tucker lemma

**Statement.** Let `n ≥ 1` and `λ : SV n → ℤ` be such that, for every `x ≠ 0`:
- `λ x ≠ 0` and `|λ x| < n`;
- `λ(−x) = −λ x`.

Then there exist `x, y ≠ 0` with `x ⪯ y` and `λ x = −λ y`.

**Proof by contradiction (Freund–Todd parity).** Assume there is no such complementary pair.

*Extended labelling.* Set `λ'(0) := n` and `λ' := λ` elsewhere. No edge through 0 is complementary, because `−n` is never a label.

*Simplices and happy simplices.*
- A *simplex* is a nonempty chain `σ ⊆ SV n` (0 allowed).
- `S(σ) := ⋃_{x∈σ} S(x)`, which equals `S(max σ)`.
- σ is *happy* if `S(σ) ⊆ λ'(σ)`.
- Let `k = |S(σ)|`. A happy simplex has `|σ| ∈ {k, k+1}`, because levels are distinct and lie in `[0, k]`, and `|λ'σ| ≤ |σ|`.

*Graph on happy simplices.*
- *Facet edge*: `σ ~ insert v σ` whenever `S(insert v σ) ⊆ λ'(σ)`.
- *Antipodal edge*: `σ ~ −σ` whenever σ is tight (`|σ| = k`) and `0 ∉ σ`.

*Degrees.* Write "full" for `|σ| = k+1` and "tight" for `|σ| = k`. ℓ* denotes the one label of a full simplex that lies outside `S(σ)`.

| happy σ | up (add a vertex) | down (remove a vertex) | antipodal | degree |
|---|---|---|---|---|
| `{0}` (full, k = 0, labels `{n}`) | 1 (add the vertex with `S = {n}`) | 0 | 0 | **1** |
| full, k ≥ 1, labels `S ∪ {ℓ*}` | 1 (F4; if `−ℓ* ∈ S`, a complementary pair already exists) | 1 (remove the carrier of ℓ*) | 0 | 2 |
| full, k ≥ 1, labels = S (one label duplicated) | 0 | 2 (remove either carrier of the duplicate) | 0 | 2 |
| tight, `0 ∈ σ` (missing level `1 ≤ ℓ < k`) | 2 (F3) | 0 | 0 | 2 |
| tight, `0 ∉ σ` (missing level 0) | 1 (insert 0) | 0 | 1 | 2 |

*Conclusion.* Exactly one vertex has odd degree. This contradicts the handshake lemma, `SimpleGraph.even_card_odd_degree_vertices`.

## D. Kneser lower bound (Matoušek's reduction)

**Setup.** Let `c` be a proper colouring of KG(n,k) with `m = n − 2k + 1` colours. For a sign vector x, let `P = x⁻¹(+)` and `N = x⁻¹(−)`.

**The labelling.**
- *Small case* (`|P| < k` and `|N| < k`): `λ x = x(min supp) · |supp x|`.
  - Its absolute value lies in `[1, 2k−2]`.
- *Big case* (`|P| ≥ k` or `|N| ≥ k`): let `c*` be the maximum colour over k-subsets of P or of N. Set `λ x = ±(2k − 1 + c*)`, with sign `+` exactly when c* is attained inside P.
  - Its absolute value lies in `[2k−1, n−1]`.
  - c* cannot be attained in both P and N, because the two witnessing sets would be disjoint with the same colour.

**Checks.**
- *Antipodal*: replacing x by −x swaps P and N, which flips the sign in both cases.
- *No complementary pair*, for `x ⪯ y` with `λ x = −λ y`:
  - *Small–small*: equal levels together with `x ⪯ y` give `x = y`, which contradicts `λ x ≠ 0`.
  - *Small–big*: the ranges of |λ| are disjoint, so this cannot happen.
  - *Big–big*: then `S ⊆ P(x) ⊆ P(y)` and `T ⊆ N(y)` are disjoint k-sets with the same colour, contradicting properness.

**Contradiction.** This labelling contradicts the octahedral Tucker lemma (C). Hence there is no proper colouring with `n − 2k + 1` colours, and `χ ≥ n − 2k + 2`.

## E. Size estimate

| Part | Estimated Lean lines |
|---|---|
| A (upper bound) | ~150 |
| B (sign vectors) | ~300 |
| C (Tucker lemma) | ~700–1200 |
| D (reduction) | ~300 |
| Glue | ~100 |
| **Total** | **~1,500–2,000** |

## F. Escalation option

If the blind probe shows Kneser–Lovász is within reach, switch the target to Schrijver's theorem. It says the *stable* Kneser subgraph (no two cyclically consecutive elements) has the same chromatic number.
- Its combinatorial proof also goes through the octahedral Tucker lemma (Ziegler 2002; Meunier 2011).
- It adds an alternating-subsequence layer on top of the reduction.
