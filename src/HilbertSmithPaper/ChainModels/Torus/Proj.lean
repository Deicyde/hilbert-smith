import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Torus

/-!
# The quotient map

The quotient map `q : ℝⁿ → 𝕋ⁿ`, coordinatewise `ℝ → ℝ/4ℤ`.
-/

namespace HSP.ChainModels.Torus

variable {n : ℕ}

/-- The quotient map `q : ℝⁿ → 𝕋ⁿ`. -/
def proj (y : EuclideanSpace ℝ (Fin n)) : Torus n :=
  fun j => (y j : AddCircle (4 : ℝ))

end HSP.ChainModels.Torus
