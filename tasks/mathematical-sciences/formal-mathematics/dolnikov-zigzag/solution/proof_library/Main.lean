import Zigzag.Defs
import Zigzag.Lab
import Zigzag.Extract

namespace Zigzag

open Finset

open scoped Classical

noncomputable section

variable {n : ℕ}

variable {F : Finset (Finset (Fin n))} {c : Finset (Fin n) → ℕ}

lemma lam_natAbs_big (s : ℕ) {x : Finset (Fin n × Bool)} (hb : Big F x) :
    (lam F c s x).natAbs = s + 1 + cstar F c x := by
  unfold lam
  rw [if_pos hb]
  split_ifs <;> omega

lemma lam_natAbs_small (s : ℕ) {x : Finset (Fin n × Bool)} (hb : ¬ Big F x) :
    (lam F c s x).natAbs = altF x := by
  unfold lam
  rw [if_neg hb]
  split_ifs <;> simp

lemma lam_pos_big (s : ℕ) {x : Finset (Fin n × Bool)} (hb : Big F x) :
    0 < lam F c s x ↔ PosMax F c x := by
  unfold lam
  rw [if_pos hb]
  split_ifs with h
  · simp only [h, iff_true]; positivity
  · have : (0 : ℤ) < ((s + 1 + cstar F c x : ℕ) : ℤ) := Nat.cast_pos.2 (by omega)
    simp only [h, iff_false, not_lt]
    omega

theorem zigzag_main (F : Finset (Finset (Fin n))) (c : Finset (Fin n) → ℕ)
    (hc : ∀ A ∈ F, ∀ B ∈ F, Disjoint A B → c A ≠ c B) (t : ℕ)
    (ht : ∀ x : Fin n → SignType,
      (∀ A ∈ F, ¬ (∀ i ∈ A, x i = 1) ∧ ¬ (∀ i ∈ A, x i = -1)) → alternation x + t ≤ n) :
    ∃ f : Fin t → Finset (Fin n), (∀ i, f i ∈ F) ∧ (∀ i j, i < j → c (f i) < c (f j)) ∧
      ∀ i j : Fin t, ((i : ℕ) + j) % 2 = 1 → Disjoint (f i) (f j) := by
  have hempty : ∅ ∉ F := fun h => hc ∅ h ∅ h (by simp) rfl
  have htn : t ≤ n := by
    have h0 := ht (fun _ => 0) (by
      intro A hA
      obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.2 (fun h => hempty (h ▸ hA))
      exact ⟨fun h => absurd (h a ha) (by decide), fun h => absurd (h a ha) (by decide)⟩)
    have hz : alternation (n := n) (fun _ => 0) = 0 := by
      simp [alternation, signSeq, blockCount]
    omega
  set s := n - t with hs_def
  have hst : s + t = n := by omega
  have hs : ∀ x : Finset (Fin n × Bool), Valid x → ¬ Big F x → altF x ≤ s := by
    intro x hx hb
    have := ht (toSign x) (by
      intro A hA
      refine ⟨fun hpos => hb ⟨A, hA, Or.inl fun i hi => ?_⟩,
              fun hneg => hb ⟨A, hA, Or.inr fun i hi => ?_⟩⟩
      · rw [mem_posS]; exact toSign_eq_one.1 (hpos i hi)
      · rw [mem_negP]; exact (toSign_eq_neg_one hx).1 (hneg i hi))
    unfold altF
    omega
  have hanti : ∀ x, Valid x → lam F c s (negS x) = - lam F c s x := fun x hx => lam_negS hc s hx
  have hcomp : ∀ x y, Valid x → Valid y → x ⊆ y → lam F c s x + lam F c s y ≠ 0 :=
    fun x y hx hy hxy => lam_hcomp hc s hs hx hy hxy
  have hlev := all_levels (lam F c s) hanti hcomp n le_rfl
  have hne : ((facets n n).filter (fun τ => PAltF (Lab (lam F c s) τ))).Nonempty := by
    apply Finset.card_pos.1
    by_contra h
    rw [Nat.pos_iff_ne_zero, not_not] at h
    rw [h] at hlev
    simp at hlev
  obtain ⟨σ, hσ⟩ := hne
  rw [mem_filter] at hσ
  obtain ⟨hσf, hσalt⟩ := hσ
  set ℓ := Lab (lam F c s) σ with hℓ
  have h0 : ∀ j, ℓ j ≠ 0 := fun j => Lab_ne_zero (lam F c s) hcomp hσf j
  have habs : ∀ i j, (ℓ i).natAbs = (ℓ j).natAbs → i = j := by
    intro i j h
    exact hσalt.1 (Lab_abs (lam F c s) hcomp hσf i j h)
  obtain ⟨g, hg1, hg2, hg3⟩ := extract_ranks hst ℓ hσalt h0 habs
  have hval : ∀ j, Valid (pre σ j) := pre_valid (mem_facets.1 hσf).1
  have hbig : ∀ i, Big F (pre σ (g i)) := by
    intro i
    by_contra hb
    have h1 := lam_natAbs_small (F := F) (c := c) s hb
    have h2 := hs _ (hval _) hb
    have h3 := hg1 i
    simp only [hℓ, Lab] at h3
    omega
  have hab : ∀ i, (ℓ (g i)).natAbs = s + 1 + cstar F c (pre σ (g i)) := by
    intro i
    exact lam_natAbs_big (F := F) (c := c) s (hbig i)
  have hpos : ∀ i, (0 < ℓ (g i) ↔ PosMax F c (pre σ (g i))) := fun i =>
    lam_pos_big (F := F) (c := c) s (hbig i)
  have hex : ∀ i, ∃ A ∈ F, (if 0 < ℓ (g i) then A ⊆ posS (pre σ (g i)) else A ⊆ negP (pre σ (g i))) ∧
      c A = cstar F c (pre σ (g i)) := by
    intro i
    by_cases hp : 0 < ℓ (g i)
    · obtain ⟨A, hA, hAs, hAc⟩ := (hpos i).1 hp
      exact ⟨A, hA, by rw [if_pos hp]; exact hAs, hAc⟩
    · have hnp : ¬ PosMax F c (pre σ (g i)) := fun h => hp ((hpos i).2 h)
      have := (not_posMax_iff hc (hval _) (hbig i)).1 hnp
      obtain ⟨A, hA, hAs, hAc⟩ := this
      exact ⟨A, hA, by rw [if_neg hp]; exact hAs, hAc⟩
  choose f hfF hfside hfc using hex
  refine ⟨f, hfF, ?_, ?_⟩
  · intro i j hij
    have h1 := hg2 i j hij
    rw [hab, hab] at h1
    rw [hfc, hfc]
    omega
  · intro i j hodd
    have hpar : ¬ ((0 < ℓ (g i)) ↔ (0 < ℓ (g j))) := by
      rw [hg3 i, hg3 j]
      have : ¬ (Even (s + (i : ℕ)) ↔ Even (s + (j : ℕ))) := by
        rw [Nat.even_iff, Nat.even_iff]; omega
      exact this
    rcases le_total (g i) (g j) with hle | hle
    · have hsub := pre_mono σ hle
      by_cases hp : 0 < ℓ (g i)
      · have hq : ¬ 0 < ℓ (g j) := fun h => hpar ⟨fun _ => h, fun _ => hp⟩
        have h1 := hfside i; rw [if_pos hp] at h1
        have h2 := hfside j; rw [if_neg hq] at h2
        exact (disjoint_posS_negP (hval (g j))).mono (h1.trans (posS_mono hsub)) h2
      · have hq : 0 < ℓ (g j) := by
          by_contra hq; exact hpar ⟨fun h => absurd h hp, fun h => absurd h hq⟩
        have h1 := hfside i; rw [if_neg hp] at h1
        have h2 := hfside j; rw [if_pos hq] at h2
        exact ((disjoint_posS_negP (hval (g j))).mono h2 (h1.trans (negP_mono hsub))).symm
    · have hsub := pre_mono σ hle
      by_cases hp : 0 < ℓ (g i)
      · have hq : ¬ 0 < ℓ (g j) := fun h => hpar ⟨fun _ => h, fun _ => hp⟩
        have h1 := hfside i; rw [if_pos hp] at h1
        have h2 := hfside j; rw [if_neg hq] at h2
        exact ((disjoint_posS_negP (hval (g i))).mono h1 (h2.trans (negP_mono hsub)))
      · have hq : 0 < ℓ (g j) := by
          by_contra hq; exact hpar ⟨fun h => absurd h hp, fun h => absurd h hq⟩
        have h1 := hfside i; rw [if_neg hp] at h1
        have h2 := hfside j; rw [if_pos hq] at h2
        exact ((disjoint_posS_negP (hval (g i))).mono (h2.trans (posS_mono hsub)) h1).symm

end

end Zigzag
