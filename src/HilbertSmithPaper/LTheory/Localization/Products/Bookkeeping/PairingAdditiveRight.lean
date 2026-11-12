import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.DualityPairing

/-!
# A duality pairing is additive in the second variable

For a duality pairing `(⊠, κ) : B × E → B''` and an object `N` of `B`, the functor
`N ⊠ - : E ⥤ B''` is additive: `1 ⊠ (g + g') = 1 ⊠ g + 1 ⊠ g'`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Prod

namespace HSP

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {B : Type u₁} [Category.{v₁} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]
  {E : Type u₂} [Category.{v₂} E] [Preadditive E] [Linear ℚ E] [HasFiniteBiproducts E]
  [DualCat E]
  {B'' : Type u₃} [Category.{v₃} B''] [Preadditive B''] [Linear ℚ B''] [HasFiniteBiproducts B'']
  [DualCat B'']

namespace DualityPairing

variable (P : DualityPairing B E B'')

/-- **A duality pairing is additive in the second variable.** -/
instance additive_curry_obj (N : B) : ((Functor.curry.obj P.tensor).obj N).Additive where
  map_add {_ _ g g'} := by
    simpa [Functor.curry_obj_obj_map] using P.map_add_right (𝟙 N) g g'

end DualityPairing

end HSP
