import Zigzag.FanStep

/-!
# Extracting the `t` largest labels of an alternating family

If `ℓ : Fin n → ℤ` is a positively alternating family of nonzero integers with pairwise
distinct absolute values, and `s + t = n`, then the `t` indices whose labels have the largest
absolute values have absolute values `≥ s + 1`, strictly increasing, and signs alternating.
-/

namespace Zigzag

open Finset

theorem extract_ranks {n s t : ℕ} (hst : s + t = n) (ℓ : Fin n → ℤ) (hℓ : PAltF ℓ)
    (h0 : ∀ j, ℓ j ≠ 0) (habs : ∀ i j, (ℓ i).natAbs = (ℓ j).natAbs → i = j) :
    ∃ g : Fin t → Fin n, (∀ i, s + 1 ≤ (ℓ (g i)).natAbs) ∧
      (∀ i i', i < i' → (ℓ (g i)).natAbs < (ℓ (g i')).natAbs) ∧
      ∀ i, (0 < ℓ (g i) ↔ Even (s + (i : ℕ))) := by
  classical
  -- the rank of an index among the absolute values
  let r : Fin n → ℕ := fun j => (univ.filter (fun j' => (ℓ j').natAbs < (ℓ j).natAbs)).card
  have r_lt : ∀ i j, (ℓ i).natAbs < (ℓ j).natAbs → r i < r j := by
    intro i j hij
    apply card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨i, by simp [hij], by simp⟩
    · intro j' hj'
      simp only [mem_filter, mem_univ, true_and] at hj' ⊢
      exact hj'.trans hij
  have r_lt_n : ∀ j, r j < n := by
    intro j
    have : (univ.filter (fun j' => (ℓ j').natAbs < (ℓ j).natAbs)) ⊂ (univ : Finset (Fin n)) := by
      rw [Finset.ssubset_iff_of_subset (subset_univ _)]
      exact ⟨j, mem_univ _, by simp⟩
    simpa using card_lt_card this
  have r_inj : Function.Injective (fun j => (⟨r j, r_lt_n j⟩ : Fin n)) := by
    intro i j hij
    have hr : r i = r j := by simpa using hij
    by_contra hne
    have hne' : (ℓ i).natAbs ≠ (ℓ j).natAbs := fun h => hne (habs i j h)
    rcases lt_or_gt_of_ne hne' with h | h
    · exact absurd (r_lt i j h) (by omega)
    · exact absurd (r_lt j i h) (by omega)
  have r_surj : Function.Surjective (fun j => (⟨r j, r_lt_n j⟩ : Fin n)) :=
    Finite.injective_iff_surjective.1 r_inj
  have hk : ∀ i : Fin t, s + (i : ℕ) < n := fun i => by have := i.2; omega
  choose g hg using fun i : Fin t => r_surj ⟨s + i, hk i⟩
  have hrg : ∀ i : Fin t, r (g i) = s + i := fun i => by
    have := congrArg Fin.val (hg i); simpa using this
  refine ⟨g, ?_, ?_, ?_⟩
  · intro i
    -- the `s + i` smaller absolute values are distinct positive integers below `|ℓ (g i)|`
    have hcard : s + (i : ℕ) ≤ (ℓ (g i)).natAbs - 1 := by
      rw [← hrg i]
      have : (univ.filter (fun j' => (ℓ j').natAbs < (ℓ (g i)).natAbs)).card ≤
          (Icc 1 ((ℓ (g i)).natAbs - 1)).card := by
        apply card_le_card_of_injOn (fun j' => (ℓ j').natAbs)
        · intro j' hj'
          simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hj'
          have := h0 j'
          simp only [coe_Icc, Set.mem_Icc]
          omega
        · intro a _ b _ hab
          exact habs a b hab
      simpa using this
    have := h0 (g i)
    omega
  · intro i i' hii
    have h1 : r (g i) < r (g i') := by rw [hrg, hrg]; have : (i : ℕ) < i' := hii; omega
    by_contra hcon
    rcases lt_or_eq_of_le (not_lt.1 hcon) with h | h
    · exact absurd (r_lt _ _ h) (by omega)
    · have := habs _ _ h
      rw [this] at h1
      exact lt_irrefl _ h1
  · intro i
    have hmem : ℓ (g i) ∈ univ.image ℓ := mem_image_of_mem _ (mem_univ _)
    have h := hℓ.2 _ hmem
    have hcount : ((univ.image ℓ).filter (fun y => y.natAbs < (ℓ (g i)).natAbs)).card = s + i := by
      rw [← hrg i, filter_image, card_image_of_injective _ hℓ.1]
    rw [h, hcount]

end Zigzag
