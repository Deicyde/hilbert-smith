import Mathlib
import HilbertSmithPaper.LocalData.Chart.Pinch

/-!
# The pinch opens the ball onto `ℝⁿ`

For `ρ > 0`, the pinch `σ_ρ` restricts to a homeomorphism from the open ball `B(0, ρ)` onto `ℝⁿ`,
with inverse `w ↦ ρ w / (1 + |w|)`. The statement asserts the existence of a homeomorphism
`h : B(0, ρ) ≃ₜ ℝⁿ` with `σ_ρ x = h x` on the ball and `h⁻¹ w = (ρ / (1 + |w|)) • w`.
-/

namespace HSP

/-- For `ρ > 0`, `σ_ρ` restricts to a homeomorphism `B(0, ρ) ≃ₜ ℝⁿ` with inverse
`w ↦ (ρ / (1 + |w|)) • w`. -/
theorem exists_pinchHomeomorph {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ h : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ρ ≃ₜ EuclideanSpace ℝ (Fin n),
      (∀ x : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ρ,
        pinch ρ ((x : EuclideanSpace ℝ (Fin n)) : OnePoint (EuclideanSpace ℝ (Fin n))) =
        ((h x : EuclideanSpace ℝ (Fin n)) : OnePoint (EuclideanSpace ℝ (Fin n)))) ∧
      ∀ w, (h.symm w : EuclideanSpace ℝ (Fin n)) = (ρ / (1 + ‖w‖)) • w := by
  set E := EuclideanSpace ℝ (Fin n)
  have hnorm : ∀ w : E, ‖(ρ / (1 + ‖w‖)) • w‖ = ρ * ‖w‖ / (1 + ‖w‖) := by
    intro w
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    ring
  have hlt : ∀ w : E, ‖(ρ / (1 + ‖w‖)) • w‖ < ρ := by
    intro w
    rw [hnorm, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg w]
  have hx : ∀ x : Metric.ball (0 : E) ρ, 0 < ρ - ‖(x : E)‖ := fun x => by
    have := x.2
    rw [Metric.mem_ball, dist_zero_right] at this
    linarith
  let h : Metric.ball (0 : E) ρ ≃ₜ E :=
    { toFun := fun x => (ρ - ‖(x : E)‖)⁻¹ • (x : E)
      invFun := fun w => ⟨(ρ / (1 + ‖w‖)) • w, by
        rw [Metric.mem_ball, dist_zero_right]; exact hlt w⟩
      left_inv := fun x => by
        apply Subtype.ext
        have h0 := hx x
        change (ρ / (1 + ‖(ρ - ‖(x : E)‖)⁻¹ • (x : E)‖)) • ((ρ - ‖(x : E)‖)⁻¹ • (x : E)) = x
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 h0), smul_smul]
        conv_rhs => rw [← one_smul ℝ (x : E)]
        congr 1
        have hρ' := hρ.ne'
        have h0' := h0.ne'
        field_simp
        rw [sub_add_cancel, div_self hρ']
      right_inv := fun w => by
        change (ρ - ‖(ρ / (1 + ‖w‖)) • w‖)⁻¹ • ((ρ / (1 + ‖w‖)) • w) = w
        rw [hnorm, smul_smul]
        conv_rhs => rw [← one_smul ℝ w]
        congr 1
        have h1 : (0 : ℝ) < 1 + ‖w‖ := by positivity
        have : ρ - ρ * ‖w‖ / (1 + ‖w‖) = ρ / (1 + ‖w‖) := by
          field_simp
          ring
        rw [this]
        field_simp
      continuous_toFun := by
        exact ((continuous_const.sub (continuous_norm.comp continuous_subtype_val)).inv₀
          fun x => (hx x).ne').smul continuous_subtype_val
      continuous_invFun := by
        refine Continuous.subtype_mk ?_ _
        exact (continuous_const.div (continuous_const.add continuous_norm)
          fun w : E => (by positivity : (0 : ℝ) < 1 + ‖w‖).ne').smul continuous_id }
  refine ⟨h, fun x => ?_, fun w => rfl⟩
  have hb : ‖(x : E)‖ < ρ := by linarith [hx x]
  change pinch ρ ((x : E) : OnePoint E) = (((ρ - ‖(x : E)‖)⁻¹ • (x : E) : E) : OnePoint E)
  simp [pinch, hb]

end HSP
