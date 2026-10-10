import Zigzag.Defs
import Zigzag.Main

namespace Zigzag

/-- Shadow `<` and `%` on ℕ: the stated conclusion becomes weaker than the real one. -/
@[instance high] def badLT : LT ℕ := ⟨fun _ _ => True⟩
@[instance high] def badMod : Mod ℕ := ⟨fun _ _ => 0⟩

theorem alternation_zigzag {n : ℕ} (F : Finset (Finset (Fin n))) (c : Finset (Fin n) → ℕ)
    (hc : ∀ A ∈ F, ∀ B ∈ F, Disjoint A B → c A ≠ c B) (t : ℕ)
    (ht : ∀ x : Fin n → SignType,
      (∀ A ∈ F, ¬ (∀ i ∈ A, x i = 1) ∧ ¬ (∀ i ∈ A, x i = -1)) → alternation x + t ≤ n) :
    ∃ f : Fin t → Finset (Fin n), (∀ i, f i ∈ F) ∧ (∀ i j, i < j → c (f i) < c (f j)) ∧
      ∀ i j : Fin t, ((i : ℕ) + j) % 2 = 1 → Disjoint (f i) (f j) := by
  obtain ⟨f, hf, -, -⟩ := zigzag_main F c hc t ht
  exact ⟨f, hf, fun _ _ _ => trivial, fun _ _ h => absurd h Nat.zero_ne_one⟩

end Zigzag
