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

end Zigzag
