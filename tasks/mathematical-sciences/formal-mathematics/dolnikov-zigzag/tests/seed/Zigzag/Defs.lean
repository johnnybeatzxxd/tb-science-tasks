import Mathlib.Combinatorics.SimpleGraph.Coloring
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
# Set systems and 2-colourings

The imports above are the part of Mathlib that is prebuilt in this environment (with all of
their dependencies). Other Mathlib modules can be imported too, but Lake then compiles them
from source.


A *set system* on `Fin n` is a `Finset (Finset (Fin n))`.  A set `A` is *monochromatic* for a
2-colouring `col : Fin n → Bool` of the ground set if all its elements receive the same colour
(in particular the empty set is monochromatic).
-/

namespace Zigzag

/-- `A` is monochromatic for the 2-colouring `col` of the ground set. -/
def Mono {n : ℕ} (col : Fin n → Bool) (A : Finset (Fin n)) : Prop :=
  ∀ i ∈ A, ∀ j ∈ A, col i = col j

/-- The set system of `/app/data/family.json`, as a finset of subsets of `Fin 6`. -/
def family : Finset (Finset (Fin 6)) :=
  {{0, 2}, {0, 1}, {1, 2, 4}, {2, 5}, {3, 4, 5}, {0, 3, 5}, {0, 4, 5}, {3, 4}, {0, 2, 4}, {3, 5}, {1, 3}, {1, 2}, {1, 4}, {0, 3}, {0, 2, 3}, {4, 5}, {0, 1, 4}, {0, 1, 5}, {2, 4}, {1, 5}, {0, 4}, {0, 1, 2}, {2, 3}, {0, 5}}

/-- The Kneser graph of a set system: two members are adjacent iff they are disjoint. -/
def kneserGraphOf {n : ℕ} (F : Finset (Finset (Fin n))) : SimpleGraph {A // A ∈ F} :=
  SimpleGraph.fromRel fun A B => Disjoint A.1 B.1

/-- `k` is the chromatic number of the Kneser graph of `family`. -/
def FamilyChromaticNumber (k : ℕ) : Prop :=
  (kneserGraphOf family).chromaticNumber = (k : ℕ∞)

end Zigzag
