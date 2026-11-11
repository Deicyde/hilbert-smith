import Mathlib
import HilbertSmithPaper.ChainModels.Torus.Proj

/-!
# Continuity of the quotient map

The quotient map `q : ℝⁿ → 𝕋ⁿ` is continuous.
-/

namespace HSP.ChainModels.Torus

variable {n : ℕ}

/-- The quotient map `q` is continuous. -/
lemma continuous_proj : Continuous (proj (n := n)) :=
  continuous_pi fun j => (AddCircle.continuous_mk' (4 : ℝ)).comp
    ((continuous_apply j).comp (PiLp.continuous_ofLp 2 _))

end HSP.ChainModels.Torus
