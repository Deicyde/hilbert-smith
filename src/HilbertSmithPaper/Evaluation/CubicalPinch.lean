import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Torus

/-!
# Cubical pinch

For `s > 0`, `a = 1/4` and `b = 1/2`, put `c_κ(x̃) = (a/s) min(1, (b - |x̃|_∞)/(b - a))` on `ℝⁿ`.
The cubical pinch `κ : 𝕋ⁿ → Sⁿ` sends `x`, with lift `x̃ ∈ [-2,2)ⁿ`, to `x̃ / c_κ(x̃)` when
`c_κ(x̃) > 0`, and to `∞` otherwise. It is continuous.

## Encoding

* `Sⁿ` is `OnePoint (EuclideanSpace ℝ (Fin n))`, as for the test map.
* `cubicalPinchScale s` is `c_κ`, with `|x̃|_∞ = ‖WithLp.ofLp x̃‖`; `cubicalPinch n s hs` (the
  declaration of the article) is `κ` as a continuous map, so the continuity proof of the article
  is part of the definition.
* Continuity: `|x̃|_∞` equals the torus norm `‖x‖` (the maximum of the circle distances from `0`),
  so `x ↦ c_κ(x̃)` is continuous. Where `c_κ > 0` we have `‖x‖ < 1/2`, the lift is continuous and
  `κ` is a quotient with positive denominator. Where `c_κ ≤ 0`, the finite values satisfy
  `|κ(x)| ≥ |x̃|_∞ / c_κ(x̃)`, which tends to `∞`.
-/

open OnePoint Filter Topology

namespace HSP.Evaluation

open HSP.ChainModels

variable {n : ℕ}

/-- The scale `c_κ(x̃) = (a/s) min(1, (b - |x̃|_∞)/(b - a))` with `a = 1/4`, `b = 1/2`. -/
noncomputable def cubicalPinchScale (s : ℝ) (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (1 / 4) / s * min 1 ((1 / 2 - ‖WithLp.ofLp y‖) / (1 / 2 - 1 / 4))

/-- The underlying function of the cubical pinch: `x̃ / c_κ(x̃)` if `c_κ(x̃) > 0`, else `∞`. -/
private noncomputable def κfun (s : ℝ) (x : Torus n) : OnePoint (EuclideanSpace ℝ (Fin n)) :=
  if 0 < cubicalPinchScale s (Torus.lift x) then
    (((cubicalPinchScale s (Torus.lift x))⁻¹ • Torus.lift x : EuclideanSpace ℝ (Fin n)) :
      OnePoint (EuclideanSpace ℝ (Fin n)))
  else ∞

private lemma scale_lift (s : ℝ) :
    (fun x : Torus n => cubicalPinchScale s (Torus.lift x)) =
      fun x => (1 / 4) / s * min 1 ((1 / 2 - ‖x‖) / (1 / 2 - 1 / 4)) := by
  funext x; simp only [cubicalPinchScale, Torus.norm_ofLp_lift]

private lemma continuous_scale_lift (s : ℝ) :
    Continuous (fun x : Torus n => cubicalPinchScale s (Torus.lift x)) := by
  rw [scale_lift]; fun_prop

private lemma continuous_κfun (s : ℝ) (hs : 0 < s) : Continuous (κfun (n := n) s) := by
  have hc := continuous_scale_lift (n := n) s
  refine continuous_iff_continuousAt.2 fun x0 => ?_
  by_cases h0 : 0 < cubicalPinchScale s (Torus.lift x0)
  · -- where `c_κ > 0`: a quotient with positive denominator
    have hx0 : ‖x0‖ < 2 := by
      by_contra hge
      have : cubicalPinchScale s (Torus.lift x0) ≤ 0 := by
        rw [cubicalPinchScale, Torus.norm_ofLp_lift]
        refine mul_nonpos_of_nonneg_of_nonpos (by positivity) ?_
        refine (min_le_right _ _).trans (div_nonpos_of_nonpos_of_nonneg ?_ (by norm_num))
        linarith
      linarith
    have hev : ∀ᶠ x in 𝓝 x0, κfun s x =
        (((cubicalPinchScale s (Torus.lift x))⁻¹ • Torus.lift x : EuclideanSpace ℝ (Fin n)) :
          OnePoint (EuclideanSpace ℝ (Fin n))) := by
      filter_upwards [hc.continuousAt.eventually (lt_mem_nhds h0)] with x hx
      simp [κfun, hx]
    refine ContinuousAt.congr ?_ (EventuallyEq.symm hev)
    exact continuous_coe.continuousAt.comp
      ((hc.continuousAt.inv₀ h0.ne').smul (Torus.continuousAt_lift x0 hx0))
  · -- where `c_κ ≤ 0`: the values tend to `∞`
    have hκ0 : κfun s x0 = ∞ := by simp [κfun, h0]
    rw [ContinuousAt, hκ0]
    refine le_nhds_infty.2 fun K _ hK => ?_
    obtain ⟨M, hM⟩ := hK.isBounded.subset_closedBall 0
    set M' := max M 1
    have hM' : 0 < M' := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hx0 : 1 / 2 ≤ ‖x0‖ := by
      by_contra hlt
      apply h0
      rw [cubicalPinchScale, Torus.norm_ofLp_lift]
      refine mul_pos (by positivity) (lt_min one_pos (div_pos ?_ (by norm_num)))
      linarith
    have e1 : ∀ᶠ x in 𝓝 x0, 1 / 4 < ‖x‖ :=
      continuous_norm.continuousAt.eventually (lt_mem_nhds (by linarith))
    have e2 : ∀ᶠ x in 𝓝 x0, cubicalPinchScale s (Torus.lift x) < 1 / (4 * M') :=
      hc.continuousAt.eventually (gt_mem_nhds (lt_of_le_of_lt (not_lt.1 h0) (by positivity)))
    rw [Filter.mem_map]
    filter_upwards [e1, e2] with x hx1 hx2
    by_cases hpos : 0 < cubicalPinchScale s (Torus.lift x)
    · left
      refine ⟨(cubicalPinchScale s (Torus.lift x))⁻¹ • Torus.lift x, ?_, by simp [κfun, hpos]⟩
      intro hv
      have hvM : ‖(cubicalPinchScale s (Torus.lift x))⁻¹ • Torus.lift x‖ ≤ M' := by
        have := hM hv; rw [Metric.mem_closedBall, dist_zero_right] at this
        exact this.trans (le_max_left _ _)
      have hnorm : ‖x‖ ≤ ‖Torus.lift x‖ := by
        rw [← Torus.norm_ofLp_lift]
        refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
        exact PiLp.norm_apply_le (Torus.lift x) j
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos] at hvM
      have h3 : (1 / (4 * M'))⁻¹ < (cubicalPinchScale s (Torus.lift x))⁻¹ :=
        (inv_lt_inv₀ (by positivity) hpos).2 hx2
      rw [one_div, inv_inv] at h3
      have ht : 1 / 4 < ‖Torus.lift x‖ := lt_of_lt_of_le hx1 hnorm
      have h5 : 4 * M' * ‖Torus.lift x‖ ≤ (cubicalPinchScale s (Torus.lift x))⁻¹ * ‖Torus.lift x‖ :=
        mul_le_mul_of_nonneg_right h3.le (norm_nonneg _)
      nlinarith
    · right
      simp [κfun, hpos]

/-- The *cubical pinch* `κ : 𝕋ⁿ → Sⁿ` for `s > 0`: `κ(x) = x̃ / c_κ(x̃)` if `c_κ(x̃) > 0`, and
`κ(x) = ∞` otherwise, where `x̃ ∈ [-2,2)ⁿ` is the lift of `x`. -/
noncomputable def cubicalPinch (n : ℕ) (s : ℝ) (hs : 0 < s) :
    C(Torus n, OnePoint (EuclideanSpace ℝ (Fin n))) :=
  ⟨κfun s, continuous_κfun s hs⟩

/-- The values of the cubical pinch. -/
lemma cubicalPinch_apply (n : ℕ) (s : ℝ) (hs : 0 < s) (x : Torus n) :
    cubicalPinch n s hs x = if 0 < cubicalPinchScale s (Torus.lift x) then
      (((cubicalPinchScale s (Torus.lift x))⁻¹ • Torus.lift x : EuclideanSpace ℝ (Fin n)) :
        OnePoint (EuclideanSpace ℝ (Fin n)))
    else ∞ := rfl

end HSP.Evaluation
