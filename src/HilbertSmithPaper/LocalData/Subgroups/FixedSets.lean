import Mathlib
import HilbertSmithPaper.LocalData.Subgroups.PadicSubgroups

/-!
# Fixed sets of the subgroups `H_j`

For an action of `ℤ_[p]` on a set `X`, `Fix_j(X)` is the set of points fixed by every element of
`H_j`.
-/

namespace HSP

/-- The fixed set `Fix_j(X) = {x ∈ X : a +ᵥ x = x for all a ∈ H_j}`. -/
def fixSet (p : ℕ) [Fact p.Prime] (X : Type*) [AddAction ℤ_[p] X] (j : ℕ) : Set X :=
  {x | ∀ a ∈ padicSubgroup p j, a +ᵥ x = x}

end HSP
