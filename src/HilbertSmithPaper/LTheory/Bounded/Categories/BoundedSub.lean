import HilbertSmithPaper.LTheory.Bounded.Categories.BoundedDuality

/-!
# The bounded subcategory

For a full subcategory `U ⊂ A`, `C_ℤ(U) ⊂ C_ℤ(A)` is the full subcategory of the objects `M` with
every `M_n` in `U`.

## Encoding

`Bounded.sub U` (the declaration of the article) is the property `fun M => ∀ n, U (M.X n)`.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace HSP

open DualCat

universe v u

namespace Bounded

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]

omit [DualCat A] in
/-- `C_ℤ(U)`: the objects of `C_ℤ(A)` with every `M_n` in `U`. -/
def sub (U : ObjectProperty A) : ObjectProperty (Bounded A) := fun M => ∀ n, U (M.X n)

end Bounded

end HSP

end
