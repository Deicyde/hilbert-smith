import HilbertSmithPaper.LTheory.Bounded.Categories.IteratedBoundedSub
import HilbertSmithPaper.LTheory.Bounded.Categories.BoundedSubAdditive

/-!
# Iterated bounded subcategories are closed under sums and duals

If `U ⊂ A` is a full additive subcategory closed under duality, so is every `C_{ℤ^j}U`, by
induction on `j`.

## Encoding

`Bounded.isDualAdditive_subPow U j` (the declaration of the article) is an instance of
`IsDualAdditive (Bounded.subPow U j)`, by recursion on `j`.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace HSP

universe v u

namespace Bounded

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A] (U : ObjectProperty A)

/-- `C_{ℤ^j}U` is a full additive subcategory closed under duality. -/
instance isDualAdditive_subPow [IsDualAdditive U] : ∀ j : ℕ, IsDualAdditive (subPow U j)
  | 0 => ‹IsDualAdditive U›
  | j + 1 => @isDualAdditive_sub (BoundedPow A j) _ _ _ _ _ (subPow U j)
    (isDualAdditive_subPow j)

end Bounded

end HSP

end
