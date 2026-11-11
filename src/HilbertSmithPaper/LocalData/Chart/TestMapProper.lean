import Mathlib
import HilbertSmithPaper.LocalData.Chart.TestMap
import HilbertSmithPaper.LocalData.Chart.OpenTestRegion

/-!
# Preimages under the test map

For a local datum, `0 < ρ < ρplus` and a compact `C ⊆ ℝⁿ`, the preimage `f⁻¹(C)` under the test map
is a compact subset of `U⁺`. Here `C` is viewed in `Sⁿ = OnePoint ℝⁿ` through the inclusion
`ℝⁿ → Sⁿ`, and `U⁺ ⊆ Ω ⊆ ℝⁿ` in `Sⁿ` through the inclusions.
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
  sorry

end HSP
