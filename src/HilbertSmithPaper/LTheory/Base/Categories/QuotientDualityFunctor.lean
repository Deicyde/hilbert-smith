import HilbertSmithPaper.LTheory.Base.Categories.FiltrationQuotient

/-!
# The quotient duality functor

The quotient functor `q : 𝒜 → 𝒜/𝒰`, `M ↦ ⟨M⟩`, `f ↦ [f]`, is a duality functor with `ξ_M`
the identity of `⟨M^*⟩`. Its strictness is in
`LTheory.Base.Categories.DualityFunctors.QuotientFunctorStrict`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]

namespace FiltQuot

variable (U : ObjectProperty A) [IsDualAdditive U]

/-- **The quotient duality functor.** The quotient functor `q : 𝒜 → 𝒜/𝒰` as a duality functor, with `ξ_M` the identity of
`⟨M^*⟩`. -/
def q : DualFunctor A (FiltQuot U) where
  toFunctor := functor U
  ξ M := Iso.refl _
  ξ_natural f := by simp [dualHom_map]
  ξ_dual M := by
    simp only [Iso.refl_hom, dualHom_id, eqToHom_refl, Category.comp_id]
    rfl

end FiltQuot

end HSP
