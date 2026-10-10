import Zigzag.Defs

/-!
# The statement to be proved

`ZigzagSpec.Statement` is the statement of `Zigzag.alternation_zigzag`, elaborated in a module that
imports only `Zigzag.Defs` and Mathlib. The verifier checks the submitted theorem against it.
-/

namespace ZigzagSpec

open Zigzag

/-- The zig-zag theorem for an arbitrary set system, with the alternation-number bound. -/
def Statement : Prop :=
  ∀ {n : ℕ} (F : Finset (Finset (Fin n))) (c : Finset (Fin n) → ℕ),
    (∀ A ∈ F, ∀ B ∈ F, Disjoint A B → c A ≠ c B) → ∀ (t : ℕ),
    (∀ x : Fin n → SignType,
      (∀ A ∈ F, ¬ (∀ i ∈ A, x i = 1) ∧ ¬ (∀ i ∈ A, x i = -1)) → alternation x + t ≤ n) →
    ∃ f : Fin t → Finset (Fin n), (∀ i, f i ∈ F) ∧ (∀ i j, i < j → c (f i) < c (f j)) ∧
      ∀ i j : Fin t, ((i : ℕ) + j) % 2 = 1 → Disjoint (f i) (f j)

end ZigzagSpec
