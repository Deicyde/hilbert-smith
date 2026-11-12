import HilbertSmithPaper.LTheory.Base.Categories.QuotientDualityFunctor
import HilbertSmithPaper.LTheory.Base.Categories.DualityFunctors.StrictDualityFunctor

/-!
# The quotient duality functor is strict

The quotient functor `q : 𝒜 → 𝒜/𝒰` is a strict duality functor: `q (M^*) = (q M)^*` and `ξ_M`
is the identity.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]

namespace FiltQuot

variable (U : ObjectProperty A) [IsDualAdditive U]

/-- The quotient functor is a strict duality functor. -/
lemma q_isStrict : (q U).IsStrict := fun _ => ⟨rfl, rfl⟩

end FiltQuot

end HSP
