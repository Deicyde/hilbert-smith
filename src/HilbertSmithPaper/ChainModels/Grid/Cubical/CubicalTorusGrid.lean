import Mathlib
import HilbertSmithPaper.ChainModels.Grid.BasedComplexTensor
import HilbertSmithPaper.ChainModels.Grid.Cubical.CircleDimNeg
import HilbertSmithPaper.ChainModels.Grid.Cubical.UnitComplex
import HilbertSmithPaper.LTheory.Localization.Products.BasedTensor

/-!
# Cubical torus grid

The grid complex `C(k) = S_k^{⊗n}` on the torus `𝕋ⁿ`: the iterated tensor product of based
complexes `(⋯((𝟙 ⊗ S_k) ⊗ S_k) ⊗ ⋯) ⊗ S_k` with `n` factors `S_k`.

## Encoding

`gridComplex k n` (the declaration of the article), with `S_k = circleComplex k` and the unit
complex `𝟙 = unitComplex`; tensoring with `𝟙` on the left changes neither the complex nor its
bases.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.ChainModels

open FreeQ

/-- The *grid complex* `C(k) = S_k^{⊗n}`: the iterated tensor product of based complexes
`(⋯((𝟙 ⊗ S_k) ⊗ S_k) ⊗ ⋯) ⊗ S_k` with `n` factors `S_k`. -/
noncomputable def gridComplex (k : ℕ) : ℕ → ChainComplex FreeQ ℤ
  | 0 => unitComplex
  | n + 1 => basedComplexTensor (gridComplex k n) (circleComplex k) (circleComplex_dim_neg k)

end HSP.ChainModels
