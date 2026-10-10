import Zigzag.Defs
import Zigzag.Main

namespace Zigzag

/-- The zig-zag theorem for an arbitrary set system, with the alternation-number bound.

Let `F` be a set system on `Fin n` and `c` a proper colouring of its Kneser graph (disjoint
members of `F` receive different colours; `c` may use any number of colours in `ℕ`). Suppose
that every sign vector `x` whose positive part and whose negative part both contain no member of
`F` has alternation number at most `n - t`. Then there are `t` members `f 0, …, f (t-1)` of `F`
with strictly increasing colours, any two of which with indices of opposite parity are
disjoint. -/
theorem alternation_zigzag {n : ℕ} (F : Finset (Finset (Fin n))) (c : Finset (Fin n) → ℕ)
    (hc : ∀ A ∈ F, ∀ B ∈ F, Disjoint A B → c A ≠ c B) (t : ℕ)
    (ht : ∀ x : Fin n → SignType,
      (∀ A ∈ F, ¬ (∀ i ∈ A, x i = 1) ∧ ¬ (∀ i ∈ A, x i = -1)) → alternation x + t ≤ n) :
    ∃ f : Fin t → Finset (Fin n), (∀ i, f i ∈ F) ∧ (∀ i j, i < j → c (f i) < c (f j)) ∧
      ∀ i j : Fin t, ((i : ℕ) + j) % 2 = 1 → Disjoint (f i) (f j) := by
  exact zigzag_main F c hc t ht

/-- An explicit proper colouring of the Kneser graph of `family` with 4 colours. -/
def familyColour (A : Finset (Fin 7)) : Fin 4 :=
  if A = {0, 2} then 2 else if A = {0, 2, 3} then 2 else if A = {0, 2, 4} then 1 else if A = {0, 3} then 2 else if A = {0, 4} then 2 else if A = {0, 5} then 2 else if A = {0, 6} then 1 else if A = {1, 3} then 0 else if A = {1, 4} then 0 else if A = {1, 4, 5} then 0 else if A = {1, 5} then 0 else if A = {2, 3, 5} then 3 else if A = {2, 4} then 3 else if A = {2, 5} then 3 else if A = {2, 6} then 1 else if A = {3, 4, 5} then 0 else if A = {4, 6} then 1 else 0

theorem familyColour_proper :
    ∀ A ∈ family, ∀ B ∈ family, Disjoint A B → familyColour A ≠ familyColour B := by
  decide +kernel

theorem family_nonempty : ∀ A ∈ family, A.Nonempty := by
  decide +kernel

/-- The alternation bound for `family`: every sign vector whose positive and negative parts
contain no member of `family` has alternation number at most 3. -/
theorem family_alternation : ∀ x : Fin 7 → SignType,
    (∀ A ∈ family, ¬ (∀ i ∈ A, x i = 1) ∧ ¬ (∀ i ∈ A, x i = -1)) → alternation x + 4 ≤ 7 := by
  decide +kernel

theorem family_colorable : (kneserGraphOf family).Colorable 4 :=
  ⟨SimpleGraph.Coloring.mk (fun A => familyColour A.1) (fun {A B} h => by
    rw [kneserGraphOf, SimpleGraph.fromRel_adj] at h
    obtain ⟨-, h | h⟩ := h
    · exact familyColour_proper _ A.2 _ B.2 h
    · exact (familyColour_proper _ B.2 _ A.2 h).symm)⟩

/-- No proper colouring with 3 colours: the zig-zag theorem with the alternation bound 4
gives 4 members of `family` with strictly increasing colours. -/
theorem family_not_colorable : ¬ (kneserGraphOf family).Colorable 3 := by
  rintro ⟨C⟩
  classical
  let c : Finset (Fin 7) → ℕ := fun A => if h : A ∈ family then (C ⟨A, h⟩ : ℕ) else 0
  have hlt : ∀ A ∈ family, c A < 3 := fun A h => by
    simp only [c, h]; exact (C ⟨A, h⟩).isLt
  have hc : ∀ A ∈ family, ∀ B ∈ family, Disjoint A B → c A ≠ c B := by
    intro A hA B hB hAB hcAB
    have hne : (⟨A, hA⟩ : {A // A ∈ family}) ≠ ⟨B, hB⟩ := by
      intro h
      have hAB' : A = B := congrArg Subtype.val h
      subst hAB'
      obtain ⟨x, hx⟩ := family_nonempty A hA
      exact Finset.disjoint_left.1 hAB hx hx
    have hadj : (kneserGraphOf family).Adj ⟨A, hA⟩ ⟨B, hB⟩ := by
      rw [kneserGraphOf, SimpleGraph.fromRel_adj]
      exact ⟨hne, Or.inl hAB⟩
    apply C.valid hadj
    simp only [c, hA, hB, dite_true] at hcAB
    exact Fin.ext hcAB
  obtain ⟨f, hf, hinc, -⟩ := alternation_zigzag family c hc 4 family_alternation
  have h0 := hinc 0 1 (by decide)
  have h1 := hinc 1 2 (by decide)
  have h2 := hinc 2 3 (by decide)
  have hlast := hlt _ (hf 3)
  omega

theorem family_chromatic_number : FamilyChromaticNumber 4 := by
  unfold FamilyChromaticNumber
  rw [show ((4 : ℕ) : ℕ∞) = (3 : ℕ) + 1 by norm_num,
    SimpleGraph.chromaticNumber_eq_iff_colorable_not_colorable]
  exact ⟨family_colorable, family_not_colorable⟩

end Zigzag
