import HilbertSmithPaper.LTheory.Base.Categories.DualAdditiveSubcategory

/-!
# All objects form a dual-closed additive subcategory

In a duality category `ℬ`, the property satisfied by every object contains a zero object, a sum
of any two of its objects, and the dual of each of its objects.
-/

open CategoryTheory CategoryTheory.Limits

open scoped ZeroObject

namespace HSP

open DualCat

universe v u

variable (B : Type u) [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

/-- **All objects form a dual-closed additive subcategory.** -/
instance isDualAdditive_top : IsDualAdditive (⊤ : ObjectProperty B) where
  exists_zero := ⟨0, trivial, isZero_zero B⟩
  exists_biprod {V W} _ _ := by
    have := hasBinaryBiproducts_of_finite_biproducts B
    exact ⟨BinaryBiproduct.bicone V W, ⟨BinaryBiproduct.isBilimit V W⟩, trivial⟩
  dual_mem _ := trivial

end HSP
