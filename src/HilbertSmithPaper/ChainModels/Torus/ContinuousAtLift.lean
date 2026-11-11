import Mathlib
import HilbertSmithPaper.ChainModels.Torus.Lift

/-!
# Continuity of the lift

The lift `x ↦ x̃` is continuous at every `x ∈ 𝕋ⁿ` with `d_∞(x, 0) < 2`.
-/

namespace HSP.ChainModels.Torus

variable {n : ℕ}

/-- The lift is continuous at every `x` with `d_∞(x, 0) < 2`. -/
lemma continuousAt_lift (x : Torus n) (hx : ‖x‖ < 2) :
    ContinuousAt (lift (n := n)) x := by
  have hj : ∀ j, x j ≠ ((-2 : ℝ) : AddCircle (4 : ℝ)) := by
    intro j h
    have h1 : ‖x j‖ = 2 := by
      rw [h, (AddCircle.norm_coe_eq_abs_iff (p := (4 : ℝ)) (by norm_num)).2 (by norm_num)]
      norm_num
    linarith [norm_le_pi_norm x j]
  have hc : ContinuousAt (fun y : Torus n => fun j =>
      ((AddCircle.equivIco 4 (-2) (y j) : Set.Ico (-2 : ℝ) (-2 + 4)) : ℝ)) x := by
    refine continuousAt_pi.2 fun j => ?_
    exact continuous_subtype_val.continuousAt.comp
      ((AddCircle.continuousAt_equivIco 4 (-2) (hj j)).comp
        (f := fun y : Torus n => y j) ((continuous_apply j).continuousAt))
  exact (PiLp.continuous_toLp 2 _).continuousAt.comp hc

end HSP.ChainModels.Torus
