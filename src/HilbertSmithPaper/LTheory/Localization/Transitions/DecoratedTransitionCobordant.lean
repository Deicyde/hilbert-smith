import Mathlib
import HilbertSmithPaper.LTheory.Localization.Transitions.DecoratedLineProduct

/-!
# The decorated transition respects cobordism

For an involution-invariant Karoubi filtration `𝒰 ⊂ 𝒜`, cobordant strict symmetric Poincaré
complexes in `Kar C_{ℤ^j}(𝒜/𝒰)` have cobordant decorated products with the line in
`Dec(C_{ℤ^{j+1}}𝒜/C_{ℤ^{j+1}}𝒰)`.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

namespace HSP

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A] {U : ObjectProperty A} [IsDualAdditive U]

/-- **The decorated transition respects cobordism.** -/
theorem decTransitionCx_cobordant (F : KaroubiFiltration U) (j : ℕ) {m m' : ℤ} (hm : m + 1 = m')
    {x y : SymPoincare (Karoubi (BoundedPow (FiltQuot U) j)) m} (h : Cobordant x y) :
    Cobordant (decTransitionCx F j hm x) (decTransitionCx F j hm y) := by
  sorry

end HSP
