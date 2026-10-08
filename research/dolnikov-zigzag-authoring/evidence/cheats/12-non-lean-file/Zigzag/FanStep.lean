import Zigzag.FanTucker

namespace Zigzag

open Finset

open scoped Classical

noncomputable section

variable {n : ℕ}

def NAltF {ι : Type*} [Fintype ι] [DecidableEq ι] (ℓ : ι → ℤ) : Prop :=
  Function.Injective ℓ ∧ NAlt (univ.image ℓ)

lemma card_filter_image_neg (L : Finset ℤ) (z : ℤ) :
    #((L.image (fun x => -x)).filter (fun y => y.natAbs < (-z).natAbs)) =
      #(L.filter (fun y => y.natAbs < z.natAbs)) := by
  rw [filter_image, card_image_of_injective _ neg_injective]
  congr 1
  apply filter_congr
  intro x _
  simp [Int.natAbs_neg]

lemma PAlt_neg (L : Finset ℤ) (h0 : ∀ x ∈ L, x ≠ 0) :
    PAlt (L.image (fun x => -x)) ↔ NAlt L := by
  unfold PAlt NAlt
  simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  apply forall₂_congr
  intro z hz
  rw [card_filter_image_neg]
  have := h0 z hz
  generalize #(L.filter (fun y => y.natAbs < z.natAbs)) = c
  rcases lt_or_gt_of_ne this with h | h <;> by_cases hE : Even c <;> simp [hE] <;> omega

lemma NAlt_neg (L : Finset ℤ) (h0 : ∀ x ∈ L, x ≠ 0) :
    NAlt (L.image (fun x => -x)) ↔ PAlt L := by
  unfold PAlt NAlt
  simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  apply forall₂_congr
  intro z hz
  rw [card_filter_image_neg]
  have := h0 z hz
  generalize #(L.filter (fun y => y.natAbs < z.natAbs)) = c
  rcases lt_or_gt_of_ne this with h | h <;> by_cases hE : Even c <;> simp [hE] <;> omega

lemma PAltF_neg {ι : Type*} [Fintype ι] [DecidableEq ι] (ℓ : ι → ℤ) (h0 : ∀ i, ℓ i ≠ 0) :
    PAltF (fun j => - ℓ j) ↔ NAltF ℓ := by
  unfold PAltF NAltF
  have : univ.image (fun j => - ℓ j) = (univ.image ℓ).image (fun x => -x) := by
    rw [image_image]; rfl
  rw [this, PAlt_neg _ (by simp [h0])]
  have : Function.Injective (fun j => - ℓ j) ↔ Function.Injective ℓ :=
    ⟨fun h a b hab => h (by simp [hab]), fun h a b hab => h (by simpa using hab)⟩
  rw [this]

lemma NAltF_neg {ι : Type*} [Fintype ι] [DecidableEq ι] (ℓ : ι → ℤ) (h0 : ∀ i, ℓ i ≠ 0) :
    NAltF (fun j => - ℓ j) ↔ PAltF ℓ := by
  unfold PAltF NAltF
  have : univ.image (fun j => - ℓ j) = (univ.image ℓ).image (fun x => -x) := by
    rw [image_image]; rfl
  rw [this, NAlt_neg _ (by simp [h0])]
  have : Function.Injective (fun j => - ℓ j) ↔ Function.Injective ℓ :=
    ⟨fun h a b hab => h (by simp [hab]), fun h a b hab => h (by simpa using hab)⟩
  rw [this]

lemma AltF_iff {ι : Type*} [Fintype ι] [DecidableEq ι] (ℓ : ι → ℤ) :
    AltF ℓ ↔ PAltF ℓ ∨ NAltF ℓ := by
  unfold AltF PAltF NAltF
  tauto

lemma exists_coord {d : ℕ} (hd : d < n) {σ : Fin (d+1) → Fin n × Bool}
    (hσ : σ ∈ facets n (d+1)) : ∃ k, (σ k).1 = ⟨d, hd⟩ := by
  obtain ⟨hinj, hlt⟩ := mem_facets.1 hσ
  let f : Fin (d+1) → Fin (d+1) := fun k => ⟨(σ k).1, hlt k⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply hinj
    have := congrArg Fin.val hab
    exact Fin.ext this
  obtain ⟨k, hk⟩ := Finite.surjective_of_injective hf ⟨d, by omega⟩
  have := congrArg Fin.val hk
  exact ⟨k, Fin.ext this⟩

lemma negσ_mem {d : ℕ} {σ : Fin d → Fin n × Bool} (hσ : σ ∈ facets n d) :
    negσ σ ∈ facets n d := by
  rw [mem_facets] at hσ ⊢
  exact hσ

lemma negσ_negσ {d : ℕ} (σ : Fin d → Fin n × Bool) : negσ (negσ σ) = σ := by
  funext k; simp [negσ]

section lam

variable (lam : Finset (Fin n × Bool) → ℤ)
  (hanti : ∀ x, Valid x → lam (negS x) = - lam x)
  (hcomp : ∀ x y, Valid x → Valid y → x ⊆ y → lam x + lam y ≠ 0)

include hanti hcomp in
lemma cardA {d : ℕ} (hd : d < n) :
    #((facets n (d+1)).filter (fun σ => PAltF (Lab lam σ))) =
      #(((facets n (d+1)).filter (fun σ => ∃ k, σ k = (⟨d, hd⟩, true))).filter
        (fun σ => AltF (Lab lam σ))) := by
  set F := facets n (d+1)
  set c : Fin n := ⟨d, hd⟩
  set Hp := F.filter (fun σ => ∃ k, σ k = (c, true))
  rw [← card_filter_add_card_filter_not (p := fun σ => ∃ k, σ k = (c, true))]
  have e1 : (F.filter (fun σ => PAltF (Lab lam σ))).filter (fun σ => ∃ k, σ k = (c, true)) =
      Hp.filter (fun σ => PAltF (Lab lam σ)) := by
    ext σ; simp only [Hp, mem_filter]; tauto
  have e2 : #((F.filter (fun σ => PAltF (Lab lam σ))).filter
      (fun σ => ¬ ∃ k, σ k = (c, true))) = #(Hp.filter (fun σ => NAltF (Lab lam σ))) := by
    apply card_nbij' negσ negσ
    · intro σ hσ
      simp only [coe_filter, mem_filter, Set.mem_setOf_eq, Hp] at hσ ⊢
      obtain ⟨⟨hF, hP⟩, hN⟩ := hσ
      refine ⟨⟨negσ_mem hF, ?_⟩, ?_⟩
      · obtain ⟨k, hk⟩ := exists_coord hd hF
        refine ⟨k, ?_⟩
        have : (σ k).2 = false := by
          by_contra h
          exact hN ⟨k, Prod.ext hk (by simpa using h)⟩
        simp [negσ, hk, this, c]
      · have : Lab lam (negσ σ) = fun j => - Lab lam σ j := funext (Lab_negσ lam hanti hF)
        rw [this, NAltF_neg _ (Lab_ne_zero lam hcomp hF)]
        exact hP
    · intro σ hσ
      simp only [coe_filter, mem_filter, Set.mem_setOf_eq, Hp] at hσ ⊢
      obtain ⟨⟨hF, ⟨k, hk⟩⟩, hN⟩ := hσ
      refine ⟨⟨negσ_mem hF, ?_⟩, ?_⟩
      · have : Lab lam (negσ σ) = fun j => - Lab lam σ j := funext (Lab_negσ lam hanti hF)
        rw [this, PAltF_neg _ (Lab_ne_zero lam hcomp hF)]
        exact hN
      · rintro ⟨k', hk'⟩
        have h1 : (σ k').1 = c := by
          have := congrArg Prod.fst hk'; simpa [negσ] using this
        have h2 : k = k' := (mem_facets.1 hF).1 (by simp [hk, h1])
        subst h2
        have := congrArg Prod.snd hk'
        simp [negσ, hk] at this
    · intro σ _; exact negσ_negσ σ
    · intro σ _; exact negσ_negσ σ
  have e3 : Hp.filter (fun σ => AltF (Lab lam σ)) =
      Hp.filter (fun σ => PAltF (Lab lam σ)) ∪ Hp.filter (fun σ => NAltF (Lab lam σ)) := by
    rw [← filter_or]
    apply filter_congr
    intro σ _
    exact AltF_iff _
  have e4 : Disjoint (Hp.filter (fun σ => PAltF (Lab lam σ)))
      (Hp.filter (fun σ => NAltF (Lab lam σ))) := by
    rw [disjoint_filter]
    intro σ _ h1 h2
    exact not_PAlt_and_NAlt (univ_nonempty.image _) ⟨h1.2, h2.2⟩
  rw [e1, e2, e3, card_union_of_disjoint e4]

include hcomp in
lemma cardB {d : ℕ} (Hp : Finset (Fin (d+1) → Fin n × Bool)) (hHp : Hp ⊆ facets n (d+1)) :
    (#(Hp.filter (fun σ => AltF (Lab lam σ))) : ZMod 2) =
      #((Hp ×ˢ (univ : Finset (Fin (d+1)))).filter (fun p => GoodF (Lab lam p.1) p.2)) := by
  rw [card_filter, card_filter]
  push_cast
  rw [sum_product]
  apply sum_congr rfl
  intro σ hσ
  rw [← count_fun (Lab lam σ) (Lab_ne_zero lam hcomp (hHp hσ)) (Lab_abs lam hcomp (hHp hσ)),
    card_filter]
  push_cast
  rfl

end lam

/-- the involution pairing up the good (facet, face) incidences -/
def invo {d : ℕ} (p : (Fin (d+1) → Fin n × Bool) × Fin (d+1)) :
    (Fin (d+1) → Fin n × Bool) × Fin (d+1) :=
  if p.2 = Fin.last d then
    (Function.update p.1 (Fin.last d) ((p.1 (Fin.last d)).1, !(p.1 (Fin.last d)).2), p.2)
  else (p.1 ∘ Equiv.swap p.2 (p.2 + 1), p.2)

lemma invo_snd {d : ℕ} (p : (Fin (d+1) → Fin n × Bool) × Fin (d+1)) : (invo p).2 = p.2 := by
  unfold invo; split_ifs <;> rfl

lemma Lab_invo (lam : Finset (Fin n × Bool) → ℤ) {d : ℕ}
    (p : (Fin (d+1) → Fin n × Bool) × Fin (d+1)) (j : Fin (d+1)) (hj : j ≠ p.2) :
    Lab lam (invo p).1 j = Lab lam p.1 j := by
  unfold invo Lab
  split_ifs with h
  · rw [pre_update]; rw [← h]; exact hj
  · rw [pre_swap _ h hj]

lemma invo_invo {d : ℕ} (p : (Fin (d+1) → Fin n × Bool) × Fin (d+1)) : invo (invo p) = p := by
  rcases p with ⟨σ, i⟩
  by_cases h : i = Fin.last d
  · subst h
    simp only [invo, if_true]
    ext k : 1
    · funext k
      by_cases hk : k = Fin.last d
      · subst hk; simp
      · simp [Function.update_of_ne hk]
    · rfl
  · simp only [invo, if_neg h]
    ext k : 1
    · funext k; simp
    · rfl

lemma invo_coord {d : ℕ} (p : (Fin (d+1) → Fin n × Bool) × Fin (d+1)) (h : p.2 = Fin.last d)
    (k : Fin (d+1)) : ((invo p).1 k).1 = (p.1 k).1 := by
  simp only [invo, if_pos h]
  by_cases hk : k = Fin.last d
  · subst hk; simp
  · simp [Function.update_of_ne hk]

lemma invo_mem {d : ℕ} (c : Fin n) (p : (Fin (d+1) → Fin n × Bool) × Fin (d+1))
    (hσ : p.1 ∈ facets n (d+1)) (hk : ∃ k, p.1 k = (c, true))
    (hfx : ¬ (p.2 = Fin.last d ∧ (p.1 (Fin.last d)).1 = c)) :
    (invo p).1 ∈ facets n (d+1) ∧ ∃ k, (invo p).1 k = (c, true) := by
  obtain ⟨hinj, hlt⟩ := mem_facets.1 hσ
  by_cases h : p.2 = Fin.last d
  · have hco := invo_coord p h
    refine ⟨mem_facets.2 ⟨fun a b hab => hinj (by simpa [hco] using hab),
      fun k => by rw [hco]; exact hlt k⟩, ?_⟩
    obtain ⟨k, hk⟩ := hk
    have hkl : k ≠ Fin.last d := by
      rintro rfl
      exact hfx ⟨h, by rw [hk]⟩
    refine ⟨k, ?_⟩
    simp only [invo, if_pos h]
    rw [Function.update_of_ne hkl, hk]
  · simp only [invo, if_neg h]
    refine ⟨mem_facets.2 ⟨fun a b hab => (Equiv.injective _) (hinj hab), fun k => hlt _⟩, ?_⟩
    obtain ⟨k, hk⟩ := hk
    exact ⟨Equiv.swap p.2 (p.2 + 1) k, by simp [hk]⟩

lemma invo_ne {d : ℕ} (p : (Fin (d+1) → Fin n × Bool) × Fin (d+1))
    (hσ : p.1 ∈ facets n (d+1)) : invo p ≠ p := by
  obtain ⟨hinj, -⟩ := mem_facets.1 hσ
  rcases p with ⟨σ, i⟩
  intro heq
  have h1 := congrArg Prod.fst heq
  by_cases h : i = Fin.last d
  · simp only [invo, if_pos h] at h1
    have := congrFun h1 (Fin.last d)
    simp only [Function.update_self] at this
    have h2 := congrArg Prod.snd this
    simp at h2
  · simp only [invo, if_neg h] at h1
    have := congrFun h1 i
    simp only [Function.comp, Equiv.swap_apply_left] at this
    have h2 : i + 1 = i := hinj (by simp [this])
    have hv : ((i+1 : Fin (d+1)) : ℕ) = (i : ℕ) + 1 :=
      Fin.val_add_one_of_lt (lt_of_le_of_ne (Fin.le_last i) h)
    have := congrArg Fin.val h2
    omega

lemma Lab_snoc (lam : Finset (Fin n × Bool) → ℤ) {d : ℕ} (τ : Fin d → Fin n × Bool)
    (w : Fin n × Bool) (j : Fin d) :
    Lab lam (Fin.snoc τ w : Fin (d+1) → Fin n × Bool) (Fin.castSucc j) = Lab lam τ j := by
  simp only [Lab]; rw [pre_snoc]

section lam2

variable (lam : Finset (Fin n × Bool) → ℤ)

lemma cardD {d : ℕ} (c : Fin n) :
    let Hp := (facets n (d+1)).filter (fun σ => ∃ k, σ k = (c, true))
    let Y := (Hp ×ˢ (univ : Finset (Fin (d+1)))).filter (fun p => GoodF (Lab lam p.1) p.2)
    (#Y : ZMod 2) = #(Y.filter (fun p => p.2 = Fin.last d ∧ (p.1 (Fin.last d)).1 = c)) := by
  intro Hp Y
  rw [← card_filter_add_card_filter_not (s := Y)
    (p := fun p => p.2 = Fin.last d ∧ (p.1 (Fin.last d)).1 = c)]
  push_cast
  suffices h : ((#(Y.filter (fun p => ¬ (p.2 = Fin.last d ∧ (p.1 (Fin.last d)).1 = c))) : ℕ)
      : ZMod 2) = 0 by
    rw [h, add_zero]
  rw [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  have hmem : ∀ p ∈ Y.filter (fun p => ¬ (p.2 = Fin.last d ∧ (p.1 (Fin.last d)).1 = c)),
      p.1 ∈ facets n (d+1) ∧ (∃ k, p.1 k = (c, true)) ∧ GoodF (Lab lam p.1) p.2 ∧
        ¬ (p.2 = Fin.last d ∧ (p.1 (Fin.last d)).1 = c) := by
    intro p hp
    simp only [Y, Hp, mem_filter, mem_product, mem_univ, and_true] at hp
    exact ⟨hp.1.1.1, hp.1.1.2, hp.1.2, hp.2⟩
  apply sum_involution (fun p _ => invo p)
  · intro _ _; decide
  · intro p hp _
    exact invo_ne p (hmem p hp).1
  · intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := hmem p hp
    obtain ⟨m1, m2⟩ := invo_mem c p h1 h2 h4
    simp only [Y, Hp, mem_filter, mem_product, mem_univ, and_true]
    refine ⟨⟨⟨m1, m2⟩, ?_⟩, ?_⟩
    · rw [invo_snd]
      rw [GoodF_congr (fun j hj => Lab_invo lam p j hj)]
      exact h3
    · rw [invo_snd]
      rintro ⟨e1, e2⟩
      apply h4
      exact ⟨e1, by rw [← invo_coord p e1]; exact e2⟩
  · intro p _
    exact invo_invo p

lemma cardE {d : ℕ} (hd : d < n) :
    let c : Fin n := ⟨d, hd⟩
    let Hp := (facets n (d+1)).filter (fun σ => ∃ k, σ k = (c, true))
    let Y := (Hp ×ˢ (univ : Finset (Fin (d+1)))).filter (fun p => GoodF (Lab lam p.1) p.2)
    (Y.filter (fun p => p.2 = Fin.last d ∧ (p.1 (Fin.last d)).1 = c)).card =
      ((facets n d).filter (fun τ => PAltF (Lab lam τ))).card := by
  intro c Hp Y
  have hLab : ∀ σ : Fin (d+1) → Fin n × Bool, ∀ j,
      Lab lam σ (Fin.castSucc j) = Lab lam (Fin.init σ) j := by
    intro σ j
    conv_lhs => rw [← Fin.snoc_init_self σ]
    exact Lab_snoc lam _ _ j
  apply card_nbij' (fun p => Fin.init p.1)
    (fun τ => ((Fin.snoc τ (c, true) : Fin (d+1) → Fin n × Bool), Fin.last d))
  · intro p hp
    simp only [Y, Hp, coe_filter, mem_filter, mem_product, mem_univ, and_true,
      Set.mem_setOf_eq] at hp ⊢
    obtain ⟨⟨⟨hF, -⟩, hG⟩, hl, hc⟩ := hp
    obtain ⟨hinj, hlt⟩ := mem_facets.1 hF
    refine ⟨mem_facets.2 ⟨fun a b hab => Fin.castSucc_injective _ (hinj hab), fun k => ?_⟩, ?_⟩
    · have h1 := hlt (Fin.castSucc k)
      have h2 : (p.1 (Fin.castSucc k)).1 ≠ c := by
        intro h
        rw [← hc] at h
        exact Fin.castSucc_ne_last k (hinj h)
      have h3 : ((p.1 (Fin.castSucc k)).1 : ℕ) ≠ d := fun h => h2 (Fin.ext h)
      simp only [Fin.init]
      omega
    · rw [hl, GoodF_last] at hG
      have : (fun j => Lab lam p.1 (Fin.castSucc j)) = Lab lam (Fin.init p.1) := funext (hLab p.1)
      rw [this] at hG
      exact hG
  · intro τ hτ
    simp only [Y, Hp, coe_filter, mem_filter, mem_product, mem_univ, and_true,
      Set.mem_setOf_eq] at hτ ⊢
    obtain ⟨hF, hP⟩ := hτ
    obtain ⟨hinj, hlt⟩ := mem_facets.1 hF
    refine ⟨⟨⟨mem_facets.2 ⟨?_, ?_⟩, Fin.last d, by simp⟩, ?_⟩, trivial, by simp [c]⟩
    · intro a b hab
      induction a using Fin.lastCases with
      | last =>
        induction b using Fin.lastCases with
        | last => rfl
        | cast b =>
          simp only [Fin.snoc_last, Fin.snoc_castSucc] at hab
          have := hlt b
          have := congrArg Fin.val hab
          simp [c] at this
          omega
      | cast a =>
        induction b using Fin.lastCases with
        | last =>
          simp only [Fin.snoc_last, Fin.snoc_castSucc] at hab
          have := hlt a
          have := congrArg Fin.val hab
          simp [c] at this
          omega
        | cast b =>
          simp only [Fin.snoc_castSucc] at hab
          rw [hinj hab]
    · intro k
      induction k using Fin.lastCases with
      | last => simp [c]
      | cast k => simp only [Fin.snoc_castSucc]; have := hlt k; omega
    · rw [GoodF_last]
      have : (fun j => Lab lam (Fin.snoc τ (c, true) : Fin (d+1) → Fin n × Bool)
          (Fin.castSucc j)) = Lab lam τ := funext (Lab_snoc lam τ (c, true))
      rw [this]
      exact hP
  · intro p hp
    simp only [Y, Hp, coe_filter, mem_filter, mem_product, mem_univ, and_true,
      Set.mem_setOf_eq] at hp
    obtain ⟨⟨⟨hF, ⟨k, hk⟩⟩, -⟩, hl, hc⟩ := hp
    have hkl : k = Fin.last d := (mem_facets.1 hF).1 (by simp [hk, hc])
    subst hkl
    rcases p with ⟨σ, i⟩
    simp only at hl hk ⊢
    subst hl
    rw [← hk, Fin.snoc_init_self]
  · intro τ _
    simp

end lam2

theorem step (lam : Finset (Fin n × Bool) → ℤ)
    (hanti : ∀ x, Valid x → lam (negS x) = - lam x)
    (hcomp : ∀ x y, Valid x → Valid y → x ⊆ y → lam x + lam y ≠ 0)
    (d : ℕ) (hd : d < n)
    (ih : (#((facets n d).filter (fun τ => PAltF (Lab lam τ))) : ZMod 2) = 1) :
    (#((facets n (d+1)).filter (fun σ => PAltF (Lab lam σ))) : ZMod 2) = 1 := by
  rw [cardA lam hanti hcomp hd, cardB lam hcomp _ (filter_subset _ _), cardD lam ⟨d, hd⟩,
    cardE lam hd]
  exact ih

theorem base (lam : Finset (Fin n × Bool) → ℤ) :
    (#((facets n 0).filter (fun τ => PAltF (Lab lam τ))) : ZMod 2) = 1 := by
  have : (facets n 0).filter (fun τ => PAltF (Lab lam τ)) = univ := by
    ext τ
    simp only [mem_filter, mem_univ, iff_true]
    refine ⟨mem_facets.2 ⟨fun a => a.elim0, fun k => k.elim0⟩, fun a => a.elim0, ?_⟩
    intro x hx
    simp at hx
  rw [this]
  simp

theorem all_levels (lam : Finset (Fin n × Bool) → ℤ)
    (hanti : ∀ x, Valid x → lam (negS x) = - lam x)
    (hcomp : ∀ x y, Valid x → Valid y → x ⊆ y → lam x + lam y ≠ 0) :
    ∀ d, d ≤ n → (#((facets n d).filter (fun τ => PAltF (Lab lam τ))) : ZMod 2) = 1 := by
  intro d
  induction d with
  | zero => intro _; exact base lam
  | succ d ih => intro hd; exact step lam hanti hcomp d (by omega) (ih (by omega))

/-- Octahedral Tucker lemma. -/
theorem tucker (m : ℕ) (lam : Finset (Fin n × Bool) → ℤ)
    (hm : ∀ x, Valid x → (lam x).natAbs ≤ m)
    (hanti : ∀ x, Valid x → lam (negS x) = - lam x)
    (hcomp : ∀ x y, Valid x → Valid y → x ⊆ y → lam x + lam y ≠ 0) : n ≤ m := by
  have h := all_levels lam hanti hcomp n le_rfl
  obtain ⟨σ, hσ⟩ : ((facets n n).filter (fun τ => PAltF (Lab lam τ))).Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro he
    rw [he] at h
    simp at h
  rw [mem_filter] at hσ
  obtain ⟨hF, hinj, -⟩ := hσ
  have hv := pre_valid (mem_facets.1 hF).1
  have := card_le_card_of_injOn (s := (univ : Finset (Fin n))) (t := Icc 1 m)
    (fun j => (Lab lam σ j).natAbs) ?_ ?_
  · simpa using this
  · intro j _
    simp only [coe_Icc, Set.mem_Icc]
    refine ⟨?_, hm _ (hv j)⟩
    have := Lab_ne_zero lam hcomp hF j
    omega
  · intro a _ b _ hab
    exact hinj (Lab_abs lam hcomp hF a b hab)

end

end Zigzag
