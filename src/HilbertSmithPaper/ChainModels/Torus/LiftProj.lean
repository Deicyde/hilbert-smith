import Mathlib
import HilbertSmithPaper.ChainModels.Torus.Lift
import HilbertSmithPaper.ChainModels.Torus.Proj

/-!
# The lift inverts the quotient map near the origin

`(q(y))~ = y` for `y ∈ ℝⁿ` with `|y| < 2`.
-/

namespace HSP.ChainModels.Torus

variable {n : ℕ}

/-- The lift of `q(y)` is `y` when `|y| < 2`. -/
lemma lift_proj (y : EuclideanSpace ℝ (Fin n)) (hy : ‖y‖ < 2) : lift (proj y) = y := by
  refine PiLp.ext fun j => ?_
  have hj : |y.ofLp j| < 2 :=
    lt_of_le_of_lt (by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le y j) hy
  rw [abs_lt] at hj
  simp only [lift, proj]
  rw [AddCircle.equivIco_coe_eq (show y.ofLp j ∈ Set.Ico (-2 : ℝ) (-2 + 4) from
    ⟨by linarith, by linarith⟩)]

end HSP.ChainModels.Torus
