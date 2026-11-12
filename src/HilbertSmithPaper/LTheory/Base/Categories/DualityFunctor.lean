import HilbertSmithPaper.LTheory.Base.Categories.DualityCategory

/-!
# Duality functor

A duality functor `(F, ξ) : A → B` between duality categories is a ℚ-linear (additive) functor
`F` with a natural isomorphism `ξ M : F (M^*) ≅ (F M)^*` such that `(ξ M)^* = ξ (M^*)`. Since
`(F M)^{**} = F M` and `F (M^{**}) = F M` hold only propositionally, the last equation is stated
with the transport along these equalities. Strictness (`HSP.DualFunctor.IsStrict`) and the
identity and composite duality functors (`HSP.DualFunctor.id`, `HSP.DualFunctor.comp`) are in
`LTheory.Base.Categories.DualityFunctors`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v₁ v₂ v₃ u₁ u₂ u₃

/-- A *duality functor* `(F, ξ) : A → B`: a ℚ-linear functor `F` with a natural isomorphism
`ξ M : F (M^*) ≅ (F M)^*` such that `(ξ M)^* = ξ (M^*)` (up to the canonical transports). -/
structure DualFunctor (A : Type u₁) [Category.{v₁} A] [Preadditive A] [Linear ℚ A]
    [HasFiniteBiproducts A] [DualCat A]
    (B : Type u₂) [Category.{v₂} B] [Preadditive B] [Linear ℚ B]
    [HasFiniteBiproducts B] [DualCat B] where
  /-- The underlying functor. -/
  toFunctor : A ⥤ B
  [additive : toFunctor.Additive]
  [linear : toFunctor.Linear ℚ]
  /-- The duality isomorphism `ξ M : F (M^*) ≅ (F M)^*`. -/
  ξ (M : A) : toFunctor.obj (dual M) ≅ dual (toFunctor.obj M)
  /-- Naturality of `ξ`. -/
  ξ_natural {M N : A} (f : M ⟶ N) :
    toFunctor.map (dualHom f) ≫ (ξ M).hom = (ξ N).hom ≫ dualHom (toFunctor.map f)
  /-- `(ξ M)^* = ξ (M^*)`, with the transports along `(F M)^{**} = F M = F (M^{**})`. -/
  ξ_dual (M : A) :
    dualHom (ξ M).hom = eqToHom ((dual_dual (toFunctor.obj M)).trans
      (congrArg toFunctor.obj (dual_dual M)).symm) ≫ (ξ (dual M)).hom

namespace DualFunctor

attribute [instance] additive linear

variable {A : Type u₁} [Category.{v₁} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]
  {B : Type u₂} [Category.{v₂} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

end DualFunctor

end HSP
