import Mathlib
import HilbertSmithPaper.ChainModels.Torus.Lift
import HilbertSmithPaper.ChainModels.Torus.Proj

/-!
# The quotient map inverts the lift

`q(x̃) = x` for `x ∈ 𝕋ⁿ`.
-/

namespace HSP.ChainModels.Torus

variable {n : ℕ}

/-- `q(x̃) = x`. -/
@[simp]
lemma proj_lift (x : Torus n) : proj (lift x) = x := by
  funext j; simp [proj, lift]

end HSP.ChainModels.Torus
