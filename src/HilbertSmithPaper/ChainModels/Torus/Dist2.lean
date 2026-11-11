import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Torus

/-!
# The quotient Euclidean metric

`d_2(x,y) = (∑ⱼ d(xⱼ,yⱼ)²)^{1/2}` on `𝕋ⁿ`, `d` the circle distance.
-/

namespace HSP.ChainModels.Torus

variable {n : ℕ}

/-- The quotient Euclidean metric `d_2(x,y) = (∑ⱼ d(xⱼ,yⱼ)²)^{1/2}`. -/
noncomputable def dist₂ (x y : Torus n) : ℝ :=
  √(∑ j, dist (x j) (y j) ^ 2)

end HSP.ChainModels.Torus
