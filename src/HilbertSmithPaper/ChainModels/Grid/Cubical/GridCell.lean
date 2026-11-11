import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Cubical.CubicalTorusGrid
import HilbertSmithPaper.ChainModels.Grid.Cubical.GridCube
import HilbertSmithPaper.ChainModels.Grid.Cubical.CircleCell

/-!
# The cube of a basis vector

The basis vector `x ⊗ y` of the summand `C(k)_p ⊠ S_{k,r-p}` of `(C(k) ⊗ S_k)_r` has the cube of
`x` followed by the cell of `y`.

## Encoding

`gridCell k n r a` (the declaration of the article), by recursion on `n`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.ChainModels

open FreeQ

/-- The cube of a basis vector of `C(k)_r`: the basis vector `x ⊗ y` of the summand
`C(k)_p ⊠ S_{k,r-p}` of `C(k) ⊗ S_k` has the cube of `x` followed by the cell of `y`. -/
noncomputable def gridCell (k : ℕ) : ∀ (n : ℕ) (r : ℤ), Fin ((gridComplex k n).X r).dim → GridCube k n
  | 0, _, _ => finZeroElim
  | n + 1, r, a =>
    let s := finSigmaFinEquiv.symm a
    let ij := finProdFinEquiv.symm s.2
    Fin.snoc (gridCell k n ((s.1 : ℕ) : ℤ) ij.1) (circleCell k (r - (s.1 : ℕ)) ij.2)

end HSP.ChainModels
