import Mathlib
import HilbertSmithPaper.LTheory.Base.Categories.KaroubiFiltration
import HilbertSmithPaper.LTheory.Localization.Boundary.ImagePair
import HilbertSmithPaper.LTheory.Localization.Decorations.DecoratedLGroup
import HilbertSmithPaper.LTheory.Base.Groups.ProjectiveLGroup

/-!
# Independence of the lift

For an involution-invariant Karoubi filtration `𝒰 ⊂ 𝒜` and strict `k`-dimensional `𝒰`-pairs `V`
over `(P, π)` and `V'` over `(P', π')` with `[q V] = [q V']` in `L^{im}_k(𝒜/𝒰)`,
`[P, π] = [P', π']` in `L^p_{k-1}(𝒰)`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A] {U : ObjectProperty A} [IsDualAdditive U]

/-- **Independence of the lift.** `𝒰`-pairs with the same image class have the same boundary
class in `L^p_{k-1}(𝒰)`. -/
theorem UPair.mk_P_eq_of_image (_F : KaroubiFiltration U) {k : ℤ} (V V' : UPair U k)
    (h : LGroup.mk V.image = LGroup.mk V'.image) :
    (LGroup.mk V.P : Lp U.FullSubcategory (k - 1)) = LGroup.mk V'.P := by
  sorry

end HSP
