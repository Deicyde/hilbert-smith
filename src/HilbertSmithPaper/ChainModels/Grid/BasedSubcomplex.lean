import Mathlib

/-!
# Based subcomplexes

For a chain complex `E` of rational vector spaces with a basis in each degree, a set of basis
elements in each degree spans a *based subcomplex* if every basis element occurring in `de`, for
`e` in the set, lies in the set; its span is then a subcomplex.

## Encoding

`IsBasedSubcomplex b S` (the declaration of the article), with `E : ChainComplex (ModuleCat ℚ) ℤ`,
bases `b r` indexed by `ι r`, and the sets `S r ⊆ ι r`.
-/

open CategoryTheory

namespace HSP.ChainModels

/-- The basis elements `S r ⊆ ι r` span a *based subcomplex* of `E`: every basis element
occurring in `de`, for `e ∈ S`, lies in `S`. -/
def IsBasedSubcomplex {E : ChainComplex (ModuleCat.{0} ℚ) ℤ} {ι : ℤ → Type}
    (b : ∀ r, Module.Basis (ι r) ℚ (E.X r)) (S : ∀ r, Set (ι r)) : Prop :=
  ∀ r, ∀ e ∈ S r, ∀ e' : ι (r - 1),
    (b (r - 1)).repr ((E.d r (r - 1)).hom (b r e)) e' ≠ 0 → e' ∈ S (r - 1)

end HSP.ChainModels
