import Mathlib
import HilbertSmithPaper.LocalData.Chart.TestMap
import HilbertSmithPaper.LocalData.Chart.OpenTestRegion
import HilbertSmithPaper.LocalData.Chart.TestMapContinuous

/-!
# Preimages under the test map

For a local datum, `0 < ρ < ρplus` and a compact `C ⊆ ℝⁿ`, the preimage `f⁻¹(C)` under the test map
is a compact subset of `U⁺`. Here `C` is viewed in `Sⁿ = OnePoint ℝⁿ` through the inclusion
`ℝⁿ → Sⁿ`, and `U⁺ ⊆ Ω ⊆ ℝⁿ` in `Sⁿ` through the inclusions.

The image of `C` in `Sⁿ` is compact, hence closed, and `f` is continuous, so `f⁻¹(C)` is a closed
subset of the compact space `Sⁿ`. If `f x ∈ C` then `f x ≠ ∞`, so `x ∈ Ω` and `|F₀ x| < ρ < ρplus`.
-/

namespace HSP

/-- For `0 < ρ < ρplus` and compact `C ⊆ ℝⁿ`, `f⁻¹(C)` is compact and contained in `U⁺`. -/
theorem LocalDatum.isCompact_testMap_preimage {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}
    (A : LocalDatum p n D ρplus) {ρ : ℝ} (hρ : 0 < ρ) (hρ' : ρ < ρplus)
    {C : Set (EuclideanSpace ℝ (Fin n))} (hC : IsCompact C) :
    IsCompact (A.testMap ρ ⁻¹' ((↑) '' C : Set (OnePoint (EuclideanSpace ℝ (Fin n))))) ∧
      A.testMap ρ ⁻¹' ((↑) '' C) ⊆
        ((↑) '' ((↑) '' A.Uplus : Set (EuclideanSpace ℝ (Fin n))) :
          Set (OnePoint (EuclideanSpace ℝ (Fin n)))) := by
  have hCc : IsClosed ((↑) '' C : Set (OnePoint (EuclideanSpace ℝ (Fin n)))) :=
    (hC.image OnePoint.continuous_coe).isClosed
  refine ⟨(hCc.preimage (A.continuous_testMap hρ hρ')).isCompact, ?_⟩
  intro q hq
  induction q using OnePoint.rec with
  | infty => simp [LocalDatum.testMap] at hq
  | coe x =>
    by_cases hx : x ∈ A.Ω
    · refine ⟨x, ⟨⟨x, hx⟩, ?_, rfl⟩, rfl⟩
      change ‖A.F₀ ⟨x, hx⟩‖ < ρplus
      by_contra hge
      have hge' : ¬ ‖A.F₀ ⟨x, hx⟩‖ < ρ := fun h => hge (h.trans hρ')
      simp [LocalDatum.testMap, hx, pinch, hge'] at hq
    · simp [LocalDatum.testMap, hx] at hq

end HSP
