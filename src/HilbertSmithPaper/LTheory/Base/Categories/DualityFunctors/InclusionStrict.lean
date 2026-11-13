import HilbertSmithPaper.LTheory.Base.Categories.SubcategoryInclusion
import HilbertSmithPaper.LTheory.Base.Categories.DualityFunctors.StrictDualityFunctor

/-!
# The inclusion of a dual-closed subcategory is strict

For a full additive subcategory `𝒰 ⊂ 𝒜` closed under duality, the inclusion `𝒰 → 𝒜` is a
strict duality functor.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A] (U : ObjectProperty A) [IsDualAdditive U]

namespace DualSubcategory

/-- The inclusion is a strict duality functor. -/
theorem incl_isStrict : (incl U).IsStrict := fun _ => ⟨rfl, rfl⟩

end DualSubcategory

end HSP
