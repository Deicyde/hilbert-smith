import HilbertSmithPaper.LTheory.Base.Pairs.FunctorPoincare
import HilbertSmithPaper.LTheory.Base.Pairs.SumOfPoincare
import HilbertSmithPaper.LTheory.Base.Pairs.Cobordism

/-!
# Duality functors on cobordism classes

The image under a duality functor of cobordant strict symmetric Poincaré complexes are cobordant,
and the image of a sum is cobordant to the sum of the images.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v₁ v₂ u₁ u₂

variable {B : Type u₁} [Category.{v₁} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]
  {B' : Type u₂} [Category.{v₂} B'] [Preadditive B'] [Linear ℚ B'] [HasFiniteBiproducts B']
  [DualCat B']

/-- A duality functor preserves cobordism, and preserves sums up to cobordism. -/
theorem SymPoincare.map_cobordant (F : DualFunctor B B') {k : ℤ} :
    (∀ x y : SymPoincare B k, Cobordant x y → Cobordant (x.map F) (y.map F)) ∧
    (∀ x y : SymPoincare B k, Cobordant ((x.sum y).map F) ((x.map F).sum (y.map F))) := by
  sorry

end HSP
