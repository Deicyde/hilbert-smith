import HilbertSmithPaper.LTheory.Bounded.Categories.BoundedSub
import HilbertSmithPaper.LTheory.Bounded.Categories.IteratedBoundedCategory

/-!
# Iterated bounded subcategories

For a full subcategory `U ⊂ A`, `C_{ℤ^j}U ⊂ C_{ℤ^j}A` is `U` for `j = 0` and `C_ℤ` of the previous
level otherwise.

## Encoding

`Bounded.subPow U j` (the declaration of the article) is defined by recursion on `j` with
`Bounded.sub`.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace HSP

universe v u

namespace Bounded

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A] (U : ObjectProperty A)

/-- `C_{ℤ^j}U ⊂ C_{ℤ^j}A`: `U` for `j = 0`, and `C_ℤ` of the previous level otherwise. -/
def subPow : ∀ j : ℕ, ObjectProperty (BoundedPow A j)
  | 0 => U
  | j + 1 => sub (subPow j)

end Bounded

end HSP

end
