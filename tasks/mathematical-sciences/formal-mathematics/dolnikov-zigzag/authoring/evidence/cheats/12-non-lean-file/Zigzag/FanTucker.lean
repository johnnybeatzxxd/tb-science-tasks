import Zigzag.FanLabels

namespace Zigzag

open Finset

open scoped Classical

noncomputable section

variable {n : ℕ}

/-- antipode of a signed set -/
def negS (x : Finset (Fin n × Bool)) : Finset (Fin n × Bool) := x.image (fun p => (p.1, !p.2))

/-- a signed set is a nonzero sign vector -/
def Valid (x : Finset (Fin n × Bool)) : Prop :=
  x.Nonempty ∧ ∀ i, ¬ ((i, true) ∈ x ∧ (i, false) ∈ x)

/-- maximal chains of the barycentric subdivision of the boundary of the `d`-dim
cross-polytope, encoded as orderings of signed coordinates `0, …, d-1`. -/
def facets (n d : ℕ) : Finset (Fin d → Fin n × Bool) :=
  univ.filter (fun σ => Function.Injective (fun k => (σ k).1) ∧ ∀ k, ((σ k).1 : ℕ) < d)

def pre {d : ℕ} (σ : Fin d → Fin n × Bool) (j : Fin d) : Finset (Fin n × Bool) :=
  (univ.filter (fun k => k ≤ j)).image σ

def Lab (lam : Finset (Fin n × Bool) → ℤ) {d : ℕ} (σ : Fin d → Fin n × Bool) : Fin d → ℤ :=
  fun j => lam (pre σ j)

def negσ {d : ℕ} (σ : Fin d → Fin n × Bool) : Fin d → Fin n × Bool :=
  fun k => ((σ k).1, !(σ k).2)

lemma mem_facets {d : ℕ} {σ : Fin d → Fin n × Bool} :
    σ ∈ facets n d ↔ Function.Injective (fun k => (σ k).1) ∧ ∀ k, ((σ k).1 : ℕ) < d := by
  simp [facets]

lemma pre_valid {d : ℕ} {σ : Fin d → Fin n × Bool} (hσ : Function.Injective (fun k => (σ k).1))
    (j : Fin d) : Valid (pre σ j) := by
  refine ⟨⟨σ j, mem_image_of_mem _ (by simp)⟩, ?_⟩
  rintro i ⟨h1, h2⟩
  simp only [pre, mem_image, mem_filter, mem_univ, true_and] at h1 h2
  obtain ⟨a, -, ha⟩ := h1
  obtain ⟨b, -, hb⟩ := h2
  have : a = b := hσ (by simp [ha, hb])
  subst this
  rw [ha] at hb
  simp at hb

lemma pre_mono {d : ℕ} (σ : Fin d → Fin n × Bool) {j j' : Fin d} (h : j ≤ j') :
    pre σ j ⊆ pre σ j' := by
  apply image_subset_image
  intro k
  simp only [mem_filter, mem_univ, true_and]
  intro hk
  exact le_trans hk h

lemma pre_negσ {d : ℕ} (σ : Fin d → Fin n × Bool) (j : Fin d) :
    pre (negσ σ) j = negS (pre σ j) := by
  rw [pre, pre, negS, image_image]
  rfl

section lam

variable (lam : Finset (Fin n × Bool) → ℤ)

lemma Lab_ne_zero (hcomp : ∀ x y, Valid x → Valid y → x ⊆ y → lam x + lam y ≠ 0)
    {d : ℕ} {σ : Fin d → Fin n × Bool} (hσ : σ ∈ facets n d) (j : Fin d) :
    Lab lam σ j ≠ 0 := by
  intro h
  have hv := pre_valid (mem_facets.1 hσ).1 j
  have := hcomp _ _ hv hv subset_rfl
  simp only [Lab] at h
  rw [h] at this
  simp at this

lemma Lab_abs (hcomp : ∀ x y, Valid x → Valid y → x ⊆ y → lam x + lam y ≠ 0)
    {d : ℕ} {σ : Fin d → Fin n × Bool} (hσ : σ ∈ facets n d) (i j : Fin d) :
    (Lab lam σ i).natAbs = (Lab lam σ j).natAbs → Lab lam σ i = Lab lam σ j := by
  intro h
  have hv := pre_valid (mem_facets.1 hσ).1
  rcases Int.natAbs_eq_natAbs_iff.1 h with h' | h'
  · exact h'
  · exfalso
    simp only [Lab] at h'
    rcases le_total i j with hij | hij
    · exact hcomp _ _ (hv i) (hv j) (pre_mono σ hij) (by omega)
    · exact hcomp _ _ (hv j) (hv i) (pre_mono σ hij) (by omega)

lemma Lab_negσ (hanti : ∀ x, Valid x → lam (negS x) = - lam x)
    {d : ℕ} {σ : Fin d → Fin n × Bool} (hσ : σ ∈ facets n d) (j : Fin d) :
    Lab lam (negσ σ) j = - Lab lam σ j := by
  simp only [Lab]
  rw [pre_negσ, hanti _ (pre_valid (mem_facets.1 hσ).1 j)]

end lam

lemma swap_le_iff {d : ℕ} {i j : Fin (d+1)} (hi : i ≠ Fin.last d) (hj : j ≠ i) (k : Fin (d+1)) :
    Equiv.swap i (i+1) k ≤ j ↔ k ≤ j := by
  have hv : ((i+1 : Fin (d+1)) : ℕ) = (i : ℕ) + 1 :=
    Fin.val_add_one_of_lt (lt_of_le_of_ne (Fin.le_last i) hi)
  have hj' : (j : ℕ) ≠ i := fun h => hj (Fin.ext h)
  rcases eq_or_ne k i with rfl | h1
  · rw [Equiv.swap_apply_left, Fin.le_def, Fin.le_def, hv]; omega
  rcases eq_or_ne k (i+1) with rfl | h2
  · rw [Equiv.swap_apply_right, Fin.le_def, Fin.le_def, hv]; omega
  rw [Equiv.swap_apply_of_ne_of_ne h1 h2]

lemma pre_swap {d : ℕ} (σ : Fin (d+1) → Fin n × Bool) {i j : Fin (d+1)} (hi : i ≠ Fin.last d)
    (hj : j ≠ i) : pre (σ ∘ Equiv.swap i (i+1)) j = pre σ j := by
  ext y
  simp only [pre, mem_image, mem_filter, mem_univ, true_and, Function.comp]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨Equiv.swap i (i+1) k, (swap_le_iff hi hj k).2 hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨Equiv.swap i (i+1) k, (swap_le_iff hi hj _).2 hk, by simp⟩

lemma pre_update {d : ℕ} (σ : Fin (d+1) → Fin n × Bool) (w : Fin n × Bool) {j : Fin (d+1)}
    (hj : j ≠ Fin.last d) : pre (Function.update σ (Fin.last d) w) j = pre σ j := by
  apply image_congr
  intro k hk
  simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hk
  have : k ≠ Fin.last d := by
    rintro rfl
    exact hj (le_antisymm (Fin.le_last _) hk)
  simp [Function.update_of_ne this]

lemma pre_snoc {d : ℕ} (τ : Fin d → Fin n × Bool) (w : Fin n × Bool) (j : Fin d) :
    pre (Fin.snoc τ w : Fin (d+1) → Fin n × Bool) (Fin.castSucc j) = pre τ j := by
  ext y
  simp only [pre, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨k, hk, rfl⟩
    have : k ≠ Fin.last d := by
      rintro rfl
      exact absurd hk (by simp [Fin.le_def])
    obtain ⟨k', rfl⟩ := Fin.exists_castSucc_eq.2 this
    exact ⟨k', by simpa using hk, by simp⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨Fin.castSucc k, by simpa using hk, by simp⟩

lemma GoodF_congr {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ ℓ' : ι → ℤ} {i : ι}
    (h : ∀ j, j ≠ i → ℓ j = ℓ' j) : GoodF ℓ i ↔ GoodF ℓ' i := by
  have h1 : (univ.erase i).image ℓ = (univ.erase i).image ℓ' := by
    apply image_congr
    intro j hj
    exact h j (mem_erase.1 hj).1
  have h2 : Set.EqOn ℓ ℓ' {j | j ≠ i} := fun j hj => h j hj
  unfold GoodF
  rw [h1]
  exact ⟨fun H => ⟨H.1.congr h2, H.2⟩, fun H => ⟨H.1.congr h2.symm, H.2⟩⟩

lemma GoodF_last {d : ℕ} (ℓ : Fin (d+1) → ℤ) :
    GoodF ℓ (Fin.last d) ↔ PAltF (fun j => ℓ (Fin.castSucc j)) := by
  have h1 : (univ.erase (Fin.last d)).image ℓ = univ.image (fun j => ℓ (Fin.castSucc j)) := by
    have : univ.image (fun j => ℓ (Fin.castSucc j)) = (univ.image Fin.castSucc).image ℓ := by
      rw [image_image]; rfl
    rw [this, Fin.image_castSucc]
    congr 1
    ext; simp
  unfold GoodF PAltF
  rw [h1]
  constructor
  · rintro ⟨H1, H2⟩
    refine ⟨fun a b hab => ?_, H2⟩
    exact Fin.castSucc_injective _ (H1 (by simp [Fin.castSucc_ne_last])
      (by simp [Fin.castSucc_ne_last]) hab)
  · rintro ⟨H1, H2⟩
    refine ⟨fun a ha b hb hab => ?_, H2⟩
    obtain ⟨a', rfl⟩ := Fin.exists_castSucc_eq.2 ha
    obtain ⟨b', rfl⟩ := Fin.exists_castSucc_eq.2 hb
    rw [H1 hab]

end

end Zigzag
