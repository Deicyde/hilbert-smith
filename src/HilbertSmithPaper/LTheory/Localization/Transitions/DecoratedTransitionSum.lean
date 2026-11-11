import Mathlib
import HilbertSmithPaper.LTheory.Base.Groups.LGroupAdd
import HilbertSmithPaper.LTheory.Localization.Transitions.DecoratedLineProduct

/-!
# The decorated transition is additive

For an involution-invariant Karoubi filtration `𝒰 ⊂ 𝒜`, the decorated product with the line of a
sum `(C ⊕ C', φ ⊕ φ')` has the class of the sum of the decorated products in
`L^{im}(C_{ℤ^{j+1}}𝒜/C_{ℤ^{j+1}}𝒰)`.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

namespace HSP

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A] {U : ObjectProperty A} [IsDualAdditive U]

/-- **The decorated transition is additive.** -/
theorem decTransitionCx_sum (F : KaroubiFiltration U) (j : ℕ) {m m' : ℤ} (hm : m + 1 = m')
    (x y : SymPoincare (Karoubi (BoundedPow (FiltQuot U) j)) m) :
    LGroup.mk (decTransitionCx F j hm (x.sum y)) =
      LGroup.mk ((decTransitionCx F j hm x).sum (decTransitionCx F j hm y)) := by
  sorry

end HSP
