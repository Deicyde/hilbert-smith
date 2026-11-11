import Mathlib
import HilbertSmithPaper.LocalData.Chart.Pinch

/-!
# The pinch is continuous

For `ρ > 0`, `σ_ρ : Sⁿ → Sⁿ` is continuous: on the open ball it is `x ↦ (ρ - |x|)⁻¹ • x`, outside
the closed ball it is constant `∞`, and at the sphere `|x| = ρ` its values tend to `∞`.
-/

open Filter Topology OnePoint Metric

namespace HSP

/-- For `ρ > 0` the pinch `σ_ρ` is continuous. -/
theorem continuous_pinch {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) :
    Continuous (pinch (n := n) ρ) := by
  set E := EuclideanSpace ℝ (Fin n)
  have hval : ∀ v : E, pinch ρ (v : OnePoint E) =
      if ‖v‖ < ρ then (((ρ - ‖v‖)⁻¹ • v : E) : OnePoint E) else ∞ := fun v => rfl
  rw [OnePoint.continuous_iff]
  refine ⟨?_, ?_⟩
  · -- near `∞` the pinch is constantly `∞`
    have hmem : (closedBall (0 : E) ρ)ᶜ ∈ coclosedCompact E :=
      (isCompact_closedBall 0 ρ).compl_mem_coclosedCompact_of_isClosed isClosed_closedBall
    refine tendsto_const_nhds.congr' (Filter.mem_of_superset hmem fun v hv => ?_)
    simp only [Set.mem_compl_iff, mem_closedBall, dist_zero_right, not_le] at hv
    simp [hval, not_lt.2 hv.le]
    rfl
  · rw [continuous_iff_continuousAt]
    intro v
    rcases lt_trichotomy ‖v‖ ρ with h | h | h
    · -- inside the ball
      have hev : (fun w : E => pinch ρ (w : OnePoint E)) =ᶠ[𝓝 v]
          fun w => ((((ρ - ‖w‖)⁻¹ • w : E)) : OnePoint E) := by
        filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds h] with w hw
        simp [hval, hw]
      refine ContinuousAt.congr ?_ hev.symm
      refine (OnePoint.continuous_coe.continuousAt).comp ?_
      have hc : ContinuousAt (fun w : E => ρ - ‖w‖) v :=
        (continuous_const.sub continuous_norm).continuousAt
      exact (hc.inv₀ (sub_ne_zero.2 h.ne')).smul continuousAt_id
    · -- on the sphere the values tend to `∞`
      have hinf : pinch ρ ((v : E) : OnePoint E) = ∞ := by simp [hval, h]
      show Tendsto (fun w : E => pinch ρ (w : OnePoint E)) (𝓝 v) (𝓝 (pinch ρ (v : OnePoint E)))
      rw [hinf, Tendsto, le_nhds_infty]
      intro s _ hsc
      obtain ⟨M, hM⟩ := hsc.isBounded.subset_closedBall (0 : E)
      set δ := ρ / (2 * (|M| + 1)) with hδ
      have hM1 : 0 < |M| + 1 := by positivity
      have hδpos : 0 < δ := by positivity
      have h2 : (|M| + 1) * δ = ρ / 2 := by rw [hδ]; field_simp
      have h4 : δ ≤ ρ / 2 :=
        div_le_div_of_nonneg_left hρ.le (by norm_num) (by linarith [abs_nonneg M])
      have hnear : ∀ᶠ w in 𝓝 v, ρ - δ < ‖w‖ :=
        (continuous_norm.tendsto v).eventually (lt_mem_nhds (by rw [h]; linarith))
      rw [Filter.mem_map]
      filter_upwards [hnear] with w (hw : ρ - δ < ‖w‖)
      simp only [Set.mem_preimage, hval]
      by_cases hw' : ‖w‖ < ρ
      · simp only [hw', ↓reduceIte]
        left
        refine ⟨_, fun hs' => ?_, rfl⟩
        have hle := hM hs'
        rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.2 (sub_pos.2 hw')), inv_mul_eq_div,
          div_le_iff₀ (sub_pos.2 hw')] at hle
        have h1 : (|M| + 1) * (ρ - ‖w‖) < (|M| + 1) * δ :=
          mul_lt_mul_of_pos_left (by linarith) hM1
        have h3 : M * (ρ - ‖w‖) ≤ (|M| + 1) * (ρ - ‖w‖) :=
          mul_le_mul_of_nonneg_right (by linarith [le_abs_self M]) (sub_pos.2 hw').le
        linarith
      · simp only [hw', ↓reduceIte]
        right
        rfl
    · -- outside the closed ball
      have hev : (fun w : E => pinch ρ (w : OnePoint E)) =ᶠ[𝓝 v] fun _ => ∞ := by
        filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds h] with w hw
        simp [hval, not_lt.2 hw.le]
      exact ContinuousAt.congr continuousAt_const hev.symm

end HSP
