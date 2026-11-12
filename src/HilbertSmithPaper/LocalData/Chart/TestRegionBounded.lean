import Mathlib
import HilbertSmithPaper.LocalData.Chart.TestRegion
import HilbertSmithPaper.LocalData.Chart.AveragedMapDisplacement

/-!
# The test region is bounded

`Z⁺ ⊆ B̄(0, ρplus + D) ⊆ B(0, 2)`, with `Z⁺` viewed in `ℝⁿ` through the inclusion of `Ω`.
-/

open Metric

namespace HSP

/-- The test region lies in `B̄(0, ρplus + D)`, which lies in `B(0, 2)`. -/
theorem LocalDatum.Zplus_subset {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}
    (A : LocalDatum p n D ρplus) :
    ((↑) '' A.Zplus : Set (EuclideanSpace ℝ (Fin n))) ⊆ closedBall 0 (ρplus + D) ∧
      closedBall (0 : EuclideanSpace ℝ (Fin n)) (ρplus + D) ⊆ ball 0 2 := by
  refine ⟨?_, closedBall_subset_ball (by linarith [A.ρplus_lt, A.D_le])⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_closedBall, dist_zero_right]
  have h1 := A.dist_F₀_le x
  have h2 : ‖A.F₀ x‖ ≤ ρplus := hx
  rw [dist_eq_norm] at h1
  have h3 := norm_sub_norm_le (x : EuclideanSpace ℝ (Fin n)) (A.F₀ x)
  rw [norm_sub_rev] at h3
  linarith

end HSP
