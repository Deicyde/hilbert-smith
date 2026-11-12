import Mathlib
import HilbertSmithPaper.LTheory.Localization.Transitions.LowerLGroup
import HilbertSmithPaper.LTheory.Localization.Transitions.TransitionMap

/-!
# Lower transition map

For `j ≥ 0` and `k ∈ ℤ`, the transition map at `m = k + j` is a homomorphism
`L^{⟨-j⟩}_k(A) → L^{⟨-j-1⟩}_k(A)`, since `L^{⟨-j⟩}_k(A) = L^p_{k+j}(C_{ℤ^j} A)` and
`k + j + 1 = k + (j + 1)`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v u

/-- **Lower transition map.** `t : L^{⟨-j⟩}_k(A) → L^{⟨-j-1⟩}_k(A)`. -/
noncomputable abbrev transitionLower (A : Type u) [Category.{v} A] [Preadditive A] [Linear ℚ A]
    [HasFiniteBiproducts A] [DualCat A] (j : ℕ) (k : ℤ) : lowerL A j k →+ lowerL A (j + 1) k :=
  transitionMap A j (m := k + j) (m' := k + ↑(j + 1)) (by push_cast; ring)

end HSP
