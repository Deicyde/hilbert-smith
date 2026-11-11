import HilbertSmithPaper.LTheory.Base.Categories.DualAdditiveSubcategory

/-!
# Maps factoring through a subcategory

For a property `𝒰` of objects of `𝒜`, `I_𝒰(M, N)` is the set of maps `M ⟶ N` that factor
through an object of `𝒰`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]

namespace FiltQuot

/-- **Maps factoring through a subcategory.** The ideal `I_𝒰(M, N)`: the maps `M ⟶ N` that factor through an object of `𝒰`. -/
def ideal (U : ObjectProperty A) {M N : A} (f : M ⟶ N) : Prop :=
  ∃ V : A, U V ∧ ∃ (a : M ⟶ V) (b : V ⟶ N), f = a ≫ b

end FiltQuot

end HSP
