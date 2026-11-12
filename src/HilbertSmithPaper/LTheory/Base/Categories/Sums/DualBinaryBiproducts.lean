import HilbertSmithPaper.LTheory.Base.Categories.DualityCategory

/-!
# A duality category has binary direct sums

The finite biproducts of a duality category give binary ones (Mathlib does not derive them by
instance); mapping cones and sums of complexes use them.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

/-- **A duality category has binary direct sums.** -/
instance DualCat.hasBinaryBiproducts : HasBinaryBiproducts B :=
  hasBinaryBiproducts_of_finite_biproducts B

end HSP
