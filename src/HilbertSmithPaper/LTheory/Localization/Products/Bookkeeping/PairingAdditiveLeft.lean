import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.DualityPairing

/-!
# A duality pairing is additive in the first variable

For a duality pairing `(⊠, κ) : B × E → B''`, the curried functor `N ↦ N ⊠ -` from `B` to the
functors `E ⥤ B''` is additive: `(f + f') ⊠ g = f ⊠ g + f' ⊠ g`.
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

/-- **A duality pairing is additive in the first variable.** -/
instance additive_curry : (Functor.curry.obj P.tensor).Additive where
  map_add {_ _ f f'} := by
    ext V
    simpa [Functor.curry_obj_map_app] using P.map_add_left f f' (𝟙 V)

end DualityPairing

end HSP
