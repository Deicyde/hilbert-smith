import HilbertSmithPaper.LTheory.Base.Categories.FiltrationQuotient
import HilbertSmithPaper.LTheory.Base.Categories.DualityFunctor

/-!
# Lift of a duality functor to a quotient

A duality functor `F : 𝒜 → ℬ` that identifies maps whose difference factors through `𝒰` induces
a duality functor `𝒜/𝒰 → ℬ` (`HSP.FiltQuot.liftDual`), equal to `F` on objects and
representatives, with the same duality isomorphism `ξ_⟨M⟩ = ξ_M`; precomposed with the quotient
functor it is `F` (`HSP.FiltQuot.liftDual_spec`).
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

namespace FiltQuot

section Lift

variable {A : Type*} [Category A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A] {B : Type*} [Category B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B] (U : ObjectProperty A) [IsDualAdditive U]

/-- The functor `𝒜/𝒰 → ℬ` induced by a functor `𝒜 → ℬ` killing the ideal of `𝒰`. -/
private abbrev liftFun (F : A ⥤ B)
    (H : ∀ (x y : A) (f₁ f₂ : x ⟶ y), rel U f₁ f₂ → F.map f₁ = F.map f₂) :
    FiltQuot U ⥤ B :=
  CategoryTheory.Quotient.lift (rel U) F H

private instance (F : A ⥤ B) [F.Additive]
    (H : ∀ (x y : A) (f₁ f₂ : x ⟶ y), rel U f₁ f₂ → F.map f₁ = F.map f₂) :
    (liftFun U F H).Additive where
  map_add {_ _ f g} := by
    obtain ⟨f, rfl⟩ := functor_map_surjective U f
    obtain ⟨g, rfl⟩ := functor_map_surjective U g
    rw [← Functor.map_add, CategoryTheory.Quotient.lift_map_functor_map,
      CategoryTheory.Quotient.lift_map_functor_map,
      CategoryTheory.Quotient.lift_map_functor_map, Functor.map_add]

private instance (F : A ⥤ B) [F.Linear ℚ]
    (H : ∀ (x y : A) (f₁ f₂ : x ⟶ y), rel U f₁ f₂ → F.map f₁ = F.map f₂) :
    (liftFun U F H).Linear ℚ where
  map_smul {_ _} f c := by
    obtain ⟨f, rfl⟩ := functor_map_surjective U f
    rw [← Functor.map_smul, CategoryTheory.Quotient.lift_map_functor_map,
      CategoryTheory.Quotient.lift_map_functor_map, Functor.map_smul]

/-- The duality functor `𝒜/𝒰 → ℬ` induced by a duality functor `𝒜 → ℬ` killing the ideal of
`𝒰`, with the same `ξ`. -/
def liftDual (F : DualFunctor A B)
    (H : ∀ (x y : A) (f₁ f₂ : x ⟶ y), rel U f₁ f₂ →
      F.toFunctor.map f₁ = F.toFunctor.map f₂) : DualFunctor (FiltQuot U) B where
  toFunctor := liftFun U F.toFunctor H
  ξ M := F.ξ M.as
  ξ_natural {M N} f := by
    obtain ⟨f, rfl⟩ := functor_map_surjective U f
    rw [dualHom_map, CategoryTheory.Quotient.lift_map_functor_map,
      CategoryTheory.Quotient.lift_map_functor_map]
    exact F.ξ_natural f
  ξ_dual M := F.ξ_dual M.as

/-- `q ⋙ L = F` for the lift `L` of `F`. -/
theorem liftDual_spec (F : DualFunctor A B)
    (H : ∀ (x y : A) (f₁ f₂ : x ⟶ y), rel U f₁ f₂ →
      F.toFunctor.map f₁ = F.toFunctor.map f₂) :
    functor U ⋙ (liftDual U F H).toFunctor = F.toFunctor :=
  CategoryTheory.Quotient.lift_spec _ _ H

end Lift

end FiltQuot

end HSP
