import Mathlib
import HilbertSmithPaper.LTheory.Base.Categories.KaroubiFiltration
import HilbertSmithPaper.LTheory.Localization.Boundary.ImagePair
import HilbertSmithPaper.LTheory.Localization.Decorations.DecoratedLGroup

/-!
# Lifting closed complexes

For an involution-invariant Karoubi filtration `𝒰 ⊂ 𝒜`, every `x ∈ L^{im}_k(𝒜/𝒰)` is the class
`[q V]` of the image of a strict `k`-dimensional `𝒰`-pair `V`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A] {U : ObjectProperty A} [IsDualAdditive U]

/-- **Lifting closed complexes.** Every `x ∈ L^{im}_k(𝒜/𝒰)` is `[q V]` for a strict
`k`-dimensional `𝒰`-pair `V`. -/
theorem UPair.exists_image_eq (_F : KaroubiFiltration U) {k : ℤ} (x : LIm U k) :
    ∃ V : UPair U k, LGroup.mk V.image = x := by
  sorry

end HSP
