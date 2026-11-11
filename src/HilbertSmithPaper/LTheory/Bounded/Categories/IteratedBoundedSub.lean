import HilbertSmithPaper.LTheory.Bounded.Categories.BoundedKaroubiFiltration
import HilbertSmithPaper.LTheory.Bounded.Categories.IteratedBoundedCategory

/-!
# Iterated bounded subcategories

For a full subcategory `U ⊂ A`, `C_{ℤ^j}U ⊂ C_{ℤ^j}A` is `U` for `j = 0` and `C_ℤ` of the previous
level otherwise. If `U` is a full additive subcategory closed under duality, so is every
`C_{ℤ^j}U`.

## Encoding

`Bounded.subPow U j` (the declaration of the article) is defined by recursion on `j` with
`Bounded.sub`; the closure property is the instance `Bounded.isDualAdditive_subPow`, by induction.
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

/-- `C_{ℤ^j}U` is a full additive subcategory closed under duality. -/
instance isDualAdditive_subPow [IsDualAdditive U] : ∀ j : ℕ, IsDualAdditive (subPow U j)
  | 0 => ‹IsDualAdditive U›
  | j + 1 => @isDualAdditive_sub (BoundedPow A j) _ _ _ _ _ (subPow U j)
    (isDualAdditive_subPow j)

end Bounded

end HSP

end
