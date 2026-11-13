import HilbertSmithPaper.LTheory.Base.Categories.DualityFunctor

/-!
# Strict duality functor

A duality functor `(F, ξ) : A → B` is *strict* if `ξ = id`: for every `M`, `F (M^*) = (F M)^*`
and `ξ M` is the identity of this object. Since the equality of objects is propositional, "the
identity" is the transport `eqToHom` along it.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v₁ v₂ u₁ u₂

namespace DualFunctor

variable {A : Type u₁} [Category.{v₁} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]
  {B : Type u₂} [Category.{v₂} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

/-- A duality functor is *strict* if `ξ = id`: every `ξ M` is the identity of
`F (M^*) = (F M)^*`. -/
def IsStrict (F : DualFunctor A B) : Prop :=
  ∀ M : A, ∃ h : F.toFunctor.obj (dual M) = dual (F.toFunctor.obj M), (F.ξ M).hom = eqToHom h

end DualFunctor

end HSP
