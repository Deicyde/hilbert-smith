import Mathlib
import HilbertSmithPaper.ChainModels.Torus.Proj
import HilbertSmithPaper.ChainModels.Torus.Dist2

/-!
# The quotient map does not increase distances

`d_2(q(y), q(y')) ≤ |y - y'|` for `y, y' ∈ ℝⁿ`.
-/

namespace HSP.ChainModels.Torus

variable {n : ℕ}

/-- `d_2(q y, q y') ≤ |y - y'|`. -/
lemma dist₂_proj_le (y y' : EuclideanSpace ℝ (Fin n)) : dist₂ (proj y) (proj y') ≤ ‖y - y'‖ := by
  rw [dist₂, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ => pow_le_pow_left₀ dist_nonneg ?_ 2)
  simp only [proj, dist_eq_norm, ← AddCircle.coe_sub, WithLp.ofLp_sub, Pi.sub_apply]
  exact QuotientAddGroup.norm_mk_le_norm

end HSP.ChainModels.Torus
