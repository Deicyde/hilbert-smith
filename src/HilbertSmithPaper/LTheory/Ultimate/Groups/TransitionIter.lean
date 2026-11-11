import HilbertSmithPaper.LTheory.Localization.Transitions.TransitionLower

/-!
# Iterated transition

The iterated transition `t^m : L^{⟨-j⟩}_k(A) → L^{⟨-j-m⟩}_k(A)`, with `t^0 = 1` and
`t^{m+1} = t ∘ t^m`, `t` the lower transition map.

## Encoding

`transitionIter A k j m` (the declaration of the article) is defined by recursion on `m`; the
target `L^{⟨-(j+m)⟩}_k(A)` is `lowerL A (j + m) k`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v u

variable (A : Type u) [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]

/-- The iterated transition `t^m : L^{⟨-j⟩}_k(A) → L^{⟨-j-m⟩}_k(A)`. -/
noncomputable def transitionIter (k : ℤ) (j : ℕ) : ∀ m : ℕ, lowerL A j k →+ lowerL A (j + m) k
  | 0 => AddMonoidHom.id _
  | m + 1 => (transitionLower A (j + m) k).comp (transitionIter k j m)

end HSP
