import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Cubical.CircleComplex

/-!
# The circle complex vanishes in negative degrees

`S_{k,q} = 0` for `q < 0`.

## Encoding

`circleComplex_dim_neg k` (the declaration of the article): the dimension in each negative degree
is `0`, the hypothesis `hD` of the tensor product of based complexes.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.ChainModels

open FreeQ

/-- `S_{k,q} = 0` for `q < 0`. -/
lemma circleComplex_dim_neg (k : ℕ) : ∀ q < 0, ((circleComplex k).X q).dim = 0 := by
  intro q hq
  rcases q with q | q
  · exact absurd hq (by simp)
  · rfl

end HSP.ChainModels
