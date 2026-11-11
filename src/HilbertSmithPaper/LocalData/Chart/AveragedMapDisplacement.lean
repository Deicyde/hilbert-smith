import Mathlib
import HilbertSmithPaper.LocalData.Chart.AveragedMap

/-!
# The averaged map moves points little

`|F₀ x - x| ≤ D`: `F₀ x - x = ∫ (a +ᵥ x - x) dμ`, whose norm is at most `D · μ(ℤ_p) = D`.
-/

open MeasureTheory

namespace HSP

/-- The averaged map moves every point of `Ω` by at most `D`. -/
theorem LocalDatum.dist_F₀_le {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}
    (A : LocalDatum p n D ρplus) (x : A.Ω) : dist (A.F₀ x) x ≤ D := by
  have hc : Continuous fun a : ℤ_[p] => ((a +ᵥ x : A.Ω) : EuclideanSpace ℝ (Fin n)) :=
    continuous_subtype_val.comp (continuous_id.vadd continuous_const)
  have hi : Integrable (fun a : ℤ_[p] => ((a +ᵥ x : A.Ω) : EuclideanSpace ℝ (Fin n)))
      (haarZp p) := hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hsub : A.F₀ x - x = ∫ a, (((a +ᵥ x : A.Ω) : EuclideanSpace ℝ (Fin n)) - x) ∂haarZp p := by
    rw [integral_sub hi (integrable_const _), integral_const]
    simp [LocalDatum.F₀]
  rw [dist_eq_norm, hsub]
  refine (norm_integral_le_of_norm_le_const (C := D)
    (Filter.Eventually.of_forall fun a => ?_)).trans
    (by simp)
  rw [← dist_eq_norm]
  exact A.dist_vadd_le a x

end HSP
