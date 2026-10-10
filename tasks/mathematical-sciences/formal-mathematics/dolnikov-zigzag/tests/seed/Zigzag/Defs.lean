import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Basic.Sign.Basic
import Mathlib.Combinatorics.SetFamily.Shadow
import Mathlib.Combinatorics.SetFamily.Intersecting
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Sym.Card
import Mathlib.Data.Int.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Push
import Mathlib.Tactic.Use
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Qify
import Mathlib.Tactic.Set
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Choose

/-!
# Set systems, sign vectors and alternation numbers

A *set system* on `Fin n` is a `Finset (Finset (Fin n))`. A *sign vector* is a function
`x : Fin n → SignType`. Its *alternation number* `alternation x` is the number of maximal blocks
of equal signs among its nonzero entries, read in increasing order of the index (for example
`+ 0 − − +` has alternation number 3, and the zero vector has alternation number 0).

The imports above are the part of Mathlib that is prebuilt in this environment (with all of
their dependencies). Other Mathlib modules can be imported too, but Lake then compiles them
from source.
-/

namespace Zigzag

/-- The number of maximal blocks of equal consecutive entries of a list. -/
def blockCount {α : Type*} [DecidableEq α] : List α → ℕ
  | [] => 0
  | [_] => 1
  | a :: b :: l => blockCount (b :: l) + if a = b then 0 else 1

/-- The signs of the nonzero entries of `x`, in increasing order of the index. -/
def signSeq {n : ℕ} (x : Fin n → SignType) : List SignType :=
  ((List.finRange n).map x).filter (· ≠ 0)

/-- The alternation number of a sign vector `x`: the number of maximal blocks of equal signs
among its nonzero entries, read in increasing order of the index. -/
def alternation {n : ℕ} (x : Fin n → SignType) : ℕ :=
  blockCount (signSeq x)

/-- The set system of `/app/data/family.json`, as a finset of subsets of `Fin 7`. -/
def family : Finset (Finset (Fin 7)) :=
  {{0, 2}, {0, 2, 3}, {0, 2, 4}, {0, 3}, {0, 4}, {0, 5}, {0, 6}, {1, 3}, {1, 4}, {1, 4, 5}, {1, 5}, {2, 3, 5}, {2, 4}, {2, 5}, {2, 6}, {3, 4, 5}, {4, 6}}

/-- The Kneser graph of a set system: two members are adjacent iff they are disjoint. -/
def kneserGraphOf {n : ℕ} (F : Finset (Finset (Fin n))) : SimpleGraph {A // A ∈ F} :=
  SimpleGraph.fromRel fun A B => Disjoint A.1 B.1

/-- `k` is the chromatic number of the Kneser graph of `family`. -/
def FamilyChromaticNumber (k : ℕ) : Prop :=
  (kneserGraphOf family).chromaticNumber = (k : ℕ∞)

end Zigzag
