import Mathlib
import HilbertSmithPaper.ChainModels.Torus.NormLift

/-!
# The torus norm is at most the Euclidean norm of the lift

`d_∞(x, 0) ≤ |x̃|` for `x ∈ 𝕋ⁿ`, `|·|` the Euclidean norm.
-/

namespace HSP.ChainModels.Torus

variable {n : ℕ}

/-- `d_∞(x, 0) ≤ |x̃|`: the maximum norm of the lift is at most its Euclidean norm. -/
lemma norm_le_norm_lift (x : Torus n) : ‖x‖ ≤ ‖lift x‖ := by
  rw [← norm_ofLp_lift]
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => PiLp.norm_apply_le _ j

end HSP.ChainModels.Torus
