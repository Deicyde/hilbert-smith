import HilbertSmithPaper.LTheory.Bounded.Categories.BoundedQuotientFunctor

/-!
# The entrywise quotient functor is strict

The entrywise quotient functor `C_ℤ(A)/C_ℤ(U) → C_ℤ(A/U)` (`HSP.Bounded.quotientFunctor U`) is a
strict duality functor: it is the identity on objects, so it commutes with the duality on objects,
and its duality isomorphism is the identity.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v u

namespace Bounded

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A] (U : ObjectProperty A) [IsDualAdditive U]

/-- **The entrywise quotient functor is strict.** -/
lemma quotientFunctor_isStrict : (quotientFunctor U).IsStrict := fun _ => ⟨rfl, rfl⟩

end Bounded

end HSP
