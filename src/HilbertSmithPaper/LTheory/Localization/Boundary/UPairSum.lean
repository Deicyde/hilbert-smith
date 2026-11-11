import Mathlib
import HilbertSmithPaper.LTheory.Base.Groups.LGroupAdd
import HilbertSmithPaper.LTheory.Localization.Boundary.ImagePair
import HilbertSmithPaper.LTheory.Localization.Decorations.DecoratedLGroup

/-!
# Sums of U-pairs

For strict `k`-dimensional `𝒰`-pairs `V` over `(P, π)` and `V'` over `(P', π')` there is a strict
`k`-dimensional `𝒰`-pair `V''` with `[q V''] = [q V] + [q V']` in `L^{im}_k(𝒜/𝒰)` and boundary
class `[P'', π''] = [P, π] + [P', π']` in `L^p_{k-1}(𝒰)`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A] {U : ObjectProperty A} [IsDualAdditive U]

/-- **Sums of U-pairs.** A `𝒰`-pair whose image class and boundary class are the sums. -/
theorem UPair.exists_add {k : ℤ} (V V' : UPair U k) :
    ∃ V'' : UPair U k, LGroup.mk V''.image = LGroup.mk V.image + LGroup.mk V'.image ∧
      (LGroup.mk V''.P : Lp U.FullSubcategory (k - 1)) = LGroup.mk V.P + LGroup.mk V'.P := by
  sorry

end HSP
