import Mathlib
import HilbertSmithPaper.LocalData.Control.FixedLocalData
import HilbertSmithPaper.LocalData.Chart.LocalDatumExists

/-!
# Fixed local data from a faithful action

A jointly continuous faithful action of `ℤ_[p]` on a connected `n`-manifold, and `0 < D ≤ 1/64`,
give some `ρplus ∈ (0, 1/4)` and fixed local data with constants `(D, ρplus)` in dimension `n`.
Manifolds are encoded as in the good-point module: `T2Space`, `ChartedSpace (EuclideanSpace ℝ
(Fin n))`, `ConnectedSpace`; the action is `AddAction` with `ContinuousVAdd` and `FaithfulVAdd`.

Take a local datum from the faithful action, the pinch radius `ρplus / 2` and the buffer radii
`(1, 2, 3, 4)`.
-/

namespace HSP

/-- Fixed local data exist for a faithful jointly continuous action of `ℤ_[p]` on a connected
`n`-manifold, for every `0 < D ≤ 1/64` and some `ρplus ∈ (0, 1/4)`. -/
theorem exists_fixedLocalData {p : ℕ} [Fact p.Prime] {n : ℕ} {M : Type*} [TopologicalSpace M]
    [T2Space M] [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [AddAction ℤ_[p] M] [ContinuousVAdd ℤ_[p] M] [FaithfulVAdd ℤ_[p] M]
    {D : ℝ} (hD : 0 < D) (hD' : D ≤ 1 / 64) :
    ∃ ρplus : ℝ, 0 < ρplus ∧ ρplus < 1 / 4 ∧ Nonempty (FixedLocalData p n D ρplus) := by
  obtain ⟨ρplus, h0, h1, ⟨A⟩⟩ := exists_localDatum (p := p) (n := n) (M := M) hD hD'
  refine ⟨ρplus, h0, h1, ⟨?_⟩⟩
  exact
    { toLocalDatum := A
      ρ := ρplus / 2
      ρ_pos := half_pos h0
      ρ_lt := half_lt_self h0
      r := 1
      R := 2
      t := 3
      u := 4
      r_pos := one_pos
      r_lt_R := by norm_num
      R_lt_t := by norm_num
      t_lt_u := by norm_num }

end HSP
