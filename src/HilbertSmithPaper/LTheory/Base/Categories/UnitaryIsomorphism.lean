import HilbertSmithPaper.LTheory.Base.Categories.DualityFunctor

/-!
# Unitary natural isomorphism

A natural isomorphism `η : F ≅ G` between the underlying functors of duality functors
`(F, ξ), (G, ζ) : A → B` is *unitary* if `η_M^* ∘ ζ_M ∘ η_{M^*} = ξ_M` for every `M`; in
diagrammatic order, `η_{M^*} ≫ ζ_M ≫ η_M^* = ξ_M` as maps `F (M^*) ⟶ (F M)^*`.

Encoding: a structure bundling the natural isomorphism with the unitarity condition as a Prop
field.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v₁ v₂ u₁ u₂

variable {A : Type u₁} [Category.{v₁} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]
  {B : Type u₂} [Category.{v₂} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

/-- A *unitary natural isomorphism* `η : F ≅ G` of duality functors `(F, ξ), (G, ζ)`: a natural
isomorphism of the underlying functors with `η_M^* ∘ ζ_M ∘ η_{M^*} = ξ_M` for every `M`. -/
structure DualFunctor.UnitaryIso (F G : DualFunctor A B) where
  /-- The natural isomorphism `η : F ≅ G`. -/
  iso : F.toFunctor ≅ G.toFunctor
  /-- Unitarity: `η_M^* ∘ ζ_M ∘ η_{M^*} = ξ_M`. -/
  unitary (M : A) :
    iso.hom.app (dual M) ≫ (G.ξ M).hom ≫ dualHom (iso.hom.app M) = (F.ξ M).hom

/-- Non-vacuity: the identity natural isomorphism of a duality functor is unitary. -/
private def unitaryIsoRefl (F : DualFunctor A B) : DualFunctor.UnitaryIso F F where
  iso := Iso.refl _
  unitary M := by simp

end HSP
