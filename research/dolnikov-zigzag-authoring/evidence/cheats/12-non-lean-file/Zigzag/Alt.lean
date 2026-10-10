import Zigzag.Defs
import Zigzag.FanTucker

/-!
# Alternation numbers of sign vectors

`blockCount` is monotone along sublists, and strictly increases when the first entry changes.
For a signed set `x` (a sign vector in the `Finset (Fin n × Bool)` encoding) we write
`toSign x : Fin n → SignType` and `altF x = alternation (toSign x)`. If `x ⊆ y` are valid signed
sets then `altF x ≤ altF y`, and equality forces the first nonzero signs of `x` and `y` to agree.
This is what makes the alternation labelling free of complementary edges.
-/

namespace Zigzag

open Finset

section blocks

variable {α : Type*} [DecidableEq α]

lemma blockCount_cons (a : α) (l : List α) :
    blockCount (a :: l) = blockCount l + if l.head? = some a then 0 else 1 := by
  cases l with
  | nil => rfl
  | cons b l =>
    show blockCount (b :: l) + (if a = b then 0 else 1) = _
    simp only [List.head?_cons, Option.some.injEq]
    by_cases h : a = b
    · subst h; simp
    · simp [h, Ne.symm h]

lemma blockCount_pos_of_ne_nil {l : List α} (hl : l ≠ []) : 0 < blockCount l := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a l =>
    rw [blockCount_cons]
    split_ifs with h
    · cases l with
      | nil => simp at h
      | cons b l' => have := blockCount_pos_of_ne_nil (l := b :: l') (by simp); omega
    · omega

/-- `blockCount` is monotone along sublists, and strictly so when the first entry changes. -/
theorem blockCount_sublist {l l' : List α} (h : l.Sublist l') :
    blockCount l ≤ blockCount l' ∧
      (l ≠ [] → l.head? ≠ l'.head? → blockCount l < blockCount l') := by
  induction h with
  | slnil => simp
  | @cons l₁ l₂ a h ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [blockCount_cons]
    refine ⟨by omega, fun hne hhead => ?_⟩
    by_cases hh : l₁.head? = l₂.head?
    · have hl₂ : l₂.head? ≠ some a := by rw [← hh]; simpa using hhead
      rw [if_neg hl₂]
      omega
    · have := ih2 hne hh
      omega
  | @cons_cons l₁ l₂ a h ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨?_, fun _ hhead => (hhead rfl).elim⟩
    rw [blockCount_cons, blockCount_cons]
    by_cases h1 : l₁.head? = some a
    · rw [if_pos h1]; split_ifs <;> omega
    · rw [if_neg h1]
      by_cases h2 : l₂.head? = some a
      · rw [if_pos h2]
        by_cases hl₁ : l₁ = []
        · subst hl₁
          have hl₂ : l₂ ≠ [] := by rintro rfl; simp at h2
          have := blockCount_pos_of_ne_nil hl₂
          simp [blockCount]; omega
        · have := ih2 hl₁ (by rw [h2]; exact h1)
          omega
      · rw [if_neg h2]; omega

theorem blockCount_map {β : Type*} [DecidableEq β] {f : α → β} (hf : Function.Injective f)
    (l : List α) : blockCount (l.map f) = blockCount l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, blockCount_cons, blockCount_cons, ih, List.head?_map]
    congr 1
    cases l.head? with
    | none => simp
    | some b => simp [hf.eq_iff]

end blocks

section signvec

variable {n : ℕ}

/-- The sign vector of a signed set. -/
def toSign (x : Finset (Fin n × Bool)) : Fin n → SignType :=
  fun i => if (i, true) ∈ x then 1 else if (i, false) ∈ x then -1 else 0

/-- The alternation number of a signed set. -/
def altF (x : Finset (Fin n × Bool)) : ℕ := alternation (toSign x)

/-- The first nonzero sign of `x` is `+`. -/
def firstSign (x : Finset (Fin n × Bool)) : Prop := (signSeq (toSign x)).head? = some 1

lemma toSign_eq_one {x : Finset (Fin n × Bool)} {i : Fin n} : toSign x i = 1 ↔ (i, true) ∈ x := by
  unfold toSign; split_ifs <;> simp_all

lemma toSign_eq_neg_one {x : Finset (Fin n × Bool)} (hx : Valid x) {i : Fin n} :
    toSign x i = -1 ↔ (i, false) ∈ x := by
  unfold toSign
  by_cases h1 : (i, true) ∈ x
  · have h2 : (i, false) ∉ x := fun h2 => hx.2 i ⟨h1, h2⟩
    simp only [h1, h2, if_true, iff_false]
    decide
  · by_cases h2 : (i, false) ∈ x
    · simp [h1, h2]
    · simp only [h1, h2, if_false, iff_false]
      decide

lemma toSign_ne_zero {x : Finset (Fin n × Bool)} {i : Fin n} :
    toSign x i ≠ 0 ↔ (i, true) ∈ x ∨ (i, false) ∈ x := by
  unfold toSign; split_ifs <;> simp_all <;> decide

lemma filter_map_sublist {β : Type*} (l : List β) (f g : β → SignType)
    (h : ∀ a ∈ l, f a ≠ 0 → g a = f a) :
    ((l.map f).filter (· ≠ 0)).Sublist ((l.map g).filter (· ≠ 0)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ih' := ih (fun b hb => h b (List.mem_cons_of_mem a hb))
    simp only [List.map_cons, List.filter_cons]
    by_cases hfa : f a ≠ 0
    · have hga : g a = f a := h a (List.mem_cons_self) hfa
      simp only [hfa, hga, ne_eq, not_false_eq_true, decide_true, if_true]
      exact ih'.cons_cons _
    · simp only [hfa, decide_false, Bool.false_eq_true, if_false]
      split_ifs
      · exact ih'.cons _
      · exact ih'

lemma signSeq_sublist {x y : Finset (Fin n × Bool)} (hy : Valid y) (hxy : x ⊆ y) :
    (signSeq (toSign x)).Sublist (signSeq (toSign y)) := by
  apply filter_map_sublist
  intro i _ hi
  rcases toSign_ne_zero.1 hi with h | h
  · rw [toSign_eq_one.2 h, toSign_eq_one.2 (hxy h)]
  · have hxv : Valid x := ⟨⟨_, h⟩, fun j hj => hy.2 j ⟨hxy hj.1, hxy hj.2⟩⟩
    rw [(toSign_eq_neg_one hxv).2 h, (toSign_eq_neg_one hy).2 (hxy h)]

lemma signSeq_ne_nil {x : Finset (Fin n × Bool)} (hx : Valid x) : signSeq (toSign x) ≠ [] := by
  obtain ⟨⟨i, b⟩, hib⟩ := hx.1
  have hi : toSign x i ≠ 0 := toSign_ne_zero.2 (by cases b <;> simp_all)
  intro h
  have : toSign x i ∈ signSeq (toSign x) := by
    unfold signSeq
    rw [List.mem_filter]
    exact ⟨List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩, by simpa using hi⟩
  rw [h] at this
  simp at this

lemma altF_pos {x : Finset (Fin n × Bool)} (hx : Valid x) : 0 < altF x :=
  blockCount_pos_of_ne_nil (signSeq_ne_nil hx)

lemma altF_mono {x y : Finset (Fin n × Bool)} (hx : Valid x) (hy : Valid y) (hxy : x ⊆ y) :
    altF x ≤ altF y ∧ (altF x = altF y → (firstSign x ↔ firstSign y)) := by
  obtain ⟨h1, h2⟩ := blockCount_sublist (signSeq_sublist hy hxy)
  refine ⟨h1, fun heq => ?_⟩
  have hhead : (signSeq (toSign x)).head? = (signSeq (toSign y)).head? := by
    by_contra hne
    have := h2 (signSeq_ne_nil hx) hne
    unfold altF alternation at heq
    omega
  unfold firstSign
  rw [hhead]

lemma toSign_negS {x : Finset (Fin n × Bool)} (hx : Valid x) (i : Fin n) :
    toSign (negS x) i = - toSign x i := by
  have h1 : (i, true) ∈ negS x ↔ (i, false) ∈ x := by
    simp only [negS, mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨j, b⟩, hj, rfl, hb⟩; cases b <;> simp_all
    · intro h; exact ⟨(i, false), h, rfl, rfl⟩
  have h2 : (i, false) ∈ negS x ↔ (i, true) ∈ x := by
    simp only [negS, mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨j, b⟩, hj, rfl, hb⟩; cases b <;> simp_all
    · intro h; exact ⟨(i, true), h, rfl, rfl⟩
  unfold toSign
  by_cases ht : (i, true) ∈ x
  · have hf : (i, false) ∉ x := fun hf => hx.2 i ⟨ht, hf⟩
    simp [h1, h2, ht, hf]
  · by_cases hf : (i, false) ∈ x
    · simp [h1, h2, ht, hf]
    · simp [h1, h2, ht, hf]

lemma signSeq_negS {x : Finset (Fin n × Bool)} (hx : Valid x) :
    signSeq (toSign (negS x)) = (signSeq (toSign x)).map (fun a => -a) := by
  unfold signSeq
  have : (List.finRange n).map (toSign (negS x)) =
      ((List.finRange n).map (toSign x)).map (fun a => -a) := by
    rw [List.map_map]; congr 1; funext i; exact toSign_negS hx i
  rw [this, List.filter_map]
  congr 1
  apply List.filter_congr
  intro a _
  simp [neg_eq_zero]

lemma altF_negS {x : Finset (Fin n × Bool)} (hx : Valid x) : altF (negS x) = altF x := by
  unfold altF alternation
  rw [signSeq_negS hx, blockCount_map neg_injective]

lemma firstSign_negS {x : Finset (Fin n × Bool)} (hx : Valid x) :
    firstSign (negS x) ↔ ¬ firstSign x := by
  unfold firstSign
  rw [signSeq_negS hx, List.head?_map]
  have hne := signSeq_ne_nil hx
  obtain ⟨a, l, hal⟩ := List.exists_cons_of_ne_nil hne
  rw [hal]
  have ha : a ≠ 0 := by
    have : a ∈ signSeq (toSign x) := by rw [hal]; exact List.mem_cons_self
    unfold signSeq at this
    simpa using (List.mem_filter.1 this).2
  simp only [List.head?_cons, Option.map_some, Option.some.injEq]
  rcases a with _ | _ | _
  · exact absurd rfl ha
  · decide
  · decide

end signvec

end Zigzag
