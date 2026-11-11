import HilbertSmithPaper.LTheory.Base.Categories.DualityFunctor

/-!
# Image of a complex under a duality functor

For a duality functor `(F, ξ) : ℬ → ℬ'` and a complex `C` in `ℬ`, the complex `F C` has chain
objects `F C_r` and differentials `F d_r`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v₁ v₂ u₁ u₂

variable {B : Type u₁} [Category.{v₁} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]
  {B' : Type u₂} [Category.{v₂} B'] [Preadditive B'] [Linear ℚ B'] [HasFiniteBiproducts B']
  [DualCat B']

/-- **Image of a complex under a duality functor.** The complex `F C`. -/
abbrev DualFunctor.mapCx (F : DualFunctor B B') (C : ChainComplex B ℤ) : ChainComplex B' ℤ :=
  (F.toFunctor.mapHomologicalComplex (ComplexShape.down ℤ)).obj C

end HSP
