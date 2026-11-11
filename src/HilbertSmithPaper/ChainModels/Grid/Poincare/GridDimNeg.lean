import Mathlib
import HilbertSmithPaper.ChainModels.Grid.CubicalTorusGrid
import HilbertSmithPaper.ChainModels.Grid.Tensor.TensorDimNeg

/-!
# The grid complex vanishes in negative degrees

`C(k)_q = 0` for `q < 0`: the unit complex is `ℚ` in degree `0`,
and a tensor product with the circle
complex vanishes in negative degrees.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.ChainModels

open FreeQ DualCat

/-- *The grid complex vanishes in negative degrees.* -/
lemma gridComplex_dim_neg (k : ℕ) : ∀ n : ℕ, ∀ q < 0, ((gridComplex k n).X q).dim = 0
  | 0 => by
    intro q hq
    rcases q with q | q
    · exact absurd hq (by simp)
    · rfl
  | n + 1 => basedComplexTensor_dim_neg (C := gridComplex k n) (circleComplex_dim_neg k)

end HSP.ChainModels
