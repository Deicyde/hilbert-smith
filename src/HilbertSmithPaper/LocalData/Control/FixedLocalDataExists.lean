import Mathlib
import HilbertSmithPaper.LocalData.Control.FixedLocalData

/-!
# Fixed local data from a faithful action

A jointly continuous faithful action of `ℤ_[p]` on a connected `n`-manifold, and `0 < D ≤ 1/64`,
give some `ρplus ∈ (0, 1/4)` and fixed local data with constants `(D, ρplus)` in dimension `n`.
Manifolds are encoded as in the good-point module: `T2Space`, `ChartedSpace (EuclideanSpace ℝ
(Fin n))`, `ConnectedSpace`; the action is `AddAction` with `ContinuousVAdd` and `FaithfulVAdd`.
-/

namespace HSP

/-- Fixed local data exist for a faithful jointly continuous action of `ℤ_[p]` on a connected
`n`-manifold, for every `0 < D ≤ 1/64` and some `ρplus ∈ (0, 1/4)`. -/
theorem exists_fixedLocalData {p : ℕ} [Fact p.Prime] {n : ℕ} {M : Type*} [TopologicalSpace M]
    [T2Space M] [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [AddAction ℤ_[p] M] [ContinuousVAdd ℤ_[p] M] [FaithfulVAdd ℤ_[p] M]
    {D : ℝ} (hD : 0 < D) (hD' : D ≤ 1 / 64) :
    ∃ ρplus : ℝ, 0 < ρplus ∧ ρplus < 1 / 4 ∧ Nonempty (FixedLocalData p n D ρplus) := by
  sorry

end HSP
