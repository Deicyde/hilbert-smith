import Mathlib
import HilbertSmithPaper.LocalData.Chart.TestRegionBounded
import HilbertSmithPaper.LocalData.Chart.AveragedMapContinuous

/-!
# The test region is compact

`Z⁺` is the closed set `{|F₀| ≤ ρplus}` of `Ω`, inside the compact ball `B̄(0, ρplus + D) ⊆ Ω`.
Compactness is in `Ω` (equivalently in `ℝⁿ`, through the embedding of the subtype).
-/

open Metric Topology

namespace HSP

/-- The test region is compact. -/
theorem LocalDatum.isCompact_Zplus {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}
    (A : LocalDatum p n D ρplus) : IsCompact A.Zplus := by
  have hsub : closedBall (0 : EuclideanSpace ℝ (Fin n)) (ρplus + D) ⊆ A.Ω :=
    A.Zplus_subset.2.trans A.ball_subset
  have hK : IsCompact ((↑) ⁻¹' closedBall (0 : EuclideanSpace ℝ (Fin n)) (ρplus + D) :
      Set A.Ω) := by
    rw [IsEmbedding.subtypeVal.isCompact_iff, Set.image_preimage_eq_of_subset
      (by rwa [Subtype.range_coe])]
    exact isCompact_closedBall _ _
  refine hK.of_isClosed_subset (isClosed_le (continuous_norm.comp A.continuous_F₀)
    continuous_const) fun x hx => ?_
  exact A.Zplus_subset.1 ⟨x, hx, rfl⟩

end HSP
