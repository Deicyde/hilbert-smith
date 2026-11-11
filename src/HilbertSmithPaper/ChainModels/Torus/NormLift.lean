import Mathlib
import HilbertSmithPaper.ChainModels.Torus.ProjLift

/-!
# The maximum norm of the lift

`|x̃|_∞ = d_∞(x, 0)`, where `|·|_∞` is the maximum norm of `ℝⁿ` (`‖WithLp.ofLp x̃‖`).
-/

namespace HSP.ChainModels.Torus

variable {n : ℕ}

/-- The lift lies in `[-2,2)ⁿ`. -/
private lemma lift_mem (x : Torus n) (j : Fin n) : lift x j ∈ Set.Ico (-2 : ℝ) 2 := by
  have h := (AddCircle.equivIco 4 (-2) (x j)).2
  norm_num at h
  exact h

/-- The coordinates of the lift: `|x̃ⱼ| = d(xⱼ, 0)`. -/
private lemma abs_lift (x : Torus n) (j : Fin n) : |lift x j| = ‖x j‖ := by
  have h := lift_mem x j
  have hx : ((lift x j : ℝ) : AddCircle (4 : ℝ)) = x j := congrFun (proj_lift x) j
  have hle : |lift x j| ≤ |(4 : ℝ)| / 2 := by
    rw [abs_le]; norm_num; constructor <;> linarith [h.1, h.2]
  calc |lift x j| = ‖((lift x j : ℝ) : AddCircle (4 : ℝ))‖ :=
        ((AddCircle.norm_coe_eq_abs_iff (p := (4 : ℝ)) (by norm_num)).2 hle).symm
    _ = ‖x j‖ := by rw [hx]

/-- `|x̃|_∞ = d_∞(x, 0)`. -/
lemma norm_ofLp_lift (x : Torus n) : ‖WithLp.ofLp (lift x)‖ = ‖x‖ := by
  have h : ∀ j, ‖WithLp.ofLp (lift x) j‖ = ‖x j‖ := fun j => by
    rw [Real.norm_eq_abs]; exact abs_lift x j
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_)
    ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_)
  · rw [h]; exact norm_le_pi_norm x j
  · rw [← h]; exact norm_le_pi_norm (WithLp.ofLp (lift x)) j

end HSP.ChainModels.Torus
