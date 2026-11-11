import Mathlib
import HilbertSmithPaper.LocalData.Chart.TestMap
import HilbertSmithPaper.LocalData.Chart.AveragedMapContinuous
import HilbertSmithPaper.LocalData.Chart.AveragedMapDisplacement
import HilbertSmithPaper.LocalData.Chart.PinchContinuous

/-!
# The test map is continuous

For `0 < ρ < ρplus`, `f` is `∞` at every `x ∈ ℝⁿ` with `|x| > ρ + D` (there `|F₀ x| > ρ` when
`x ∈ Ω`), and `ρ + D < 2`, so `f` agrees with the continuous `σ_ρ ∘ F₀` on the open set `Ω` and
with `∞` on the open set `{|x| > ρ + D}` together with `∞`; these cover `Sⁿ`.
-/

open Filter Topology OnePoint Metric

namespace HSP

/-- For `0 < ρ < ρplus` the test map is continuous. -/
theorem LocalDatum.continuous_testMap {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}
    (A : LocalDatum p n D ρplus) {ρ : ℝ} (hρ : 0 < ρ) (hρ' : ρ < ρplus) :
    Continuous (A.testMap ρ) := by
  set E := EuclideanSpace ℝ (Fin n)
  have hbig : ∀ x : E, ρ + D < ‖x‖ → A.testMap ρ (x : OnePoint E) = ∞ := by
    intro x hx
    by_cases hxΩ : x ∈ A.Ω
    · have h1 := A.dist_F₀_le ⟨x, hxΩ⟩
      rw [dist_eq_norm, norm_sub_rev] at h1
      have h2 := norm_sub_norm_le x (A.F₀ ⟨x, hxΩ⟩)
      have h3 : ¬ ‖A.F₀ ⟨x, hxΩ⟩‖ < ρ := fun h => by
        change ‖x - A.F₀ ⟨x, hxΩ⟩‖ ≤ D at h1
        linarith
      simp [LocalDatum.testMap, hxΩ, pinch, h3]
    · simp [LocalDatum.testMap, hxΩ]
  rw [OnePoint.continuous_iff]
  refine ⟨?_, ?_⟩
  · have hmem : (closedBall (0 : E) (ρ + D))ᶜ ∈ coclosedCompact E :=
      (isCompact_closedBall _ _).compl_mem_coclosedCompact_of_isClosed isClosed_closedBall
    refine tendsto_const_nhds.congr' (mem_of_superset hmem fun x hx => ?_)
    simp only [Set.mem_compl_iff, mem_closedBall, dist_zero_right, not_le] at hx
    change A.testMap ρ ∞ = A.testMap ρ (x : OnePoint E)
    rw [hbig x hx]
    rfl
  · rw [continuous_iff_continuousAt]
    intro v
    by_cases hv : v ∈ A.Ω
    · have hcont : ContinuousOn (fun x : E => A.testMap ρ (x : OnePoint E)) A.Ω := by
        rw [continuousOn_iff_continuous_domRestrict]
        have : A.Ω.domRestrict (fun x : E => A.testMap ρ (x : OnePoint E)) =
            fun y : A.Ω => pinch ρ ((A.F₀ y : E) : OnePoint E) := by
          funext y
          simp [LocalDatum.testMap, Set.domRestrict, y.2]
        rw [this]
        exact (continuous_pinch hρ).comp (OnePoint.continuous_coe.comp A.continuous_F₀)
      exact hcont.continuousAt (A.isOpen_Ω.mem_nhds hv)
    · have h2 : 2 ≤ ‖v‖ := by
        by_contra h
        exact hv (A.ball_subset (by simpa using not_le.1 h))
      have hlt : ρ + D < ‖v‖ := by linarith [A.ρplus_lt, A.D_le]
      refine ContinuousAt.congr (continuousAt_const (y := (∞ : OnePoint E))) ?_
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hlt] with x hx
      exact (hbig x hx).symm

end HSP
