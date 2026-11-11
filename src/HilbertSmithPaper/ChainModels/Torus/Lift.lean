import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Torus

/-!
# The lift

The lift `x̃ ∈ [-2,2)ⁿ` of `x ∈ 𝕋ⁿ`: the representative with coordinates in `[-2,2)`, as a vector of
`ℝⁿ = EuclideanSpace ℝ (Fin n)`.
-/

namespace HSP.ChainModels.Torus

variable {n : ℕ}

/-- The lift `x̃ ∈ [-2,2)ⁿ` of `x ∈ 𝕋ⁿ`, as a vector of `ℝⁿ`. -/
noncomputable def lift (x : Torus n) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun j => (AddCircle.equivIco 4 (-2) (x j) : ℝ)

end HSP.ChainModels.Torus
