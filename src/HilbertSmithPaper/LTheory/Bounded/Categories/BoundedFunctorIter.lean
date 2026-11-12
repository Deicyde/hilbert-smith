import HilbertSmithPaper.LTheory.Bounded.Categories.BoundedFunctor

/-!
# Iterated bounded extension

For a duality functor `(F, ξ) : A → A'`, the iterated bounded extension
`C_{ℤ^j}(F, ξ) : C_{ℤ^j}(A) → C_{ℤ^j}(A')` is `F` for `j = 0` and the bounded extension of
`C_{ℤ^{j-1}}(F, ξ)` otherwise.

## Encoding

`Bounded.mapIter F j` (the declaration of the article) is defined by recursion on `j`, with
`Bounded.map` the bounded extension.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace HSP

open DualCat

universe v₁ v₂ u₁ u₂

namespace Bounded

variable {A : Type u₁} [Category.{v₁} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]
  {A' : Type u₂} [Category.{v₂} A'] [Preadditive A'] [Linear ℚ A'] [HasFiniteBiproducts A']
  [DualCat A']

/-- The iterate `C_{ℤ^j}(F, ξ) : C_{ℤ^j}(A) → C_{ℤ^j}(A')`. -/
def mapIter (F : DualFunctor A A') : ∀ j : ℕ, DualFunctor (BoundedPow A j) (BoundedPow A' j)
  | 0 => F
  | j + 1 => map (mapIter F j)

end Bounded

end HSP

end
