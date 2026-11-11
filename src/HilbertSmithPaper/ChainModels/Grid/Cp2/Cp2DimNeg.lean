import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Cp2.Cp2Complex

/-!
# The cells of CP² vanish in negative degrees

The cellular chain complex `P` of `CP²` has `P_q = 0` for `q < 0`.

## Encoding

`cp2Complex_dim_neg` (the declaration of the article) says the based vector space in each
negative degree has dimension `0`, the hypothesis `hD` of the tensor product of based complexes.
-/

namespace HSP.ChainModels

/-- `P_q = 0` for `q < 0`. -/
lemma cp2Complex_dim_neg : ∀ q < 0, (cp2Complex.X q).dim = 0 := by
  intro q hq
  rcases q with q | q
  · exact absurd hq (by simp)
  · rfl

end HSP.ChainModels
