import Mathlib

/-!
# Reduction to one chart

A faithful jointly continuous action of `ℤ_[p]` on a connected `n`-manifold `M` (Hausdorff,
charted on `ℝⁿ`, no countability assumption) yields a nonempty connected open set `O ⊆ ℝⁿ` with a
faithful jointly continuous action of `ℤ_[p]`. "Nonempty connected" is `IsConnected O`; the
action on `O` is an `AddAction` on the subtype, existentially quantified.

The statement is in place; its proof (via the good point, small displacement, the basis
property of the `H_j` and the classification of closed subgroups) is still `sorry`.
-/

namespace HSP

/-- **Reduction to one chart.** A faithful jointly continuous action of `ℤ_[p]` on a connected
`n`-manifold gives a faithful jointly continuous action of `ℤ_[p]` on a nonempty connected open
subset of `ℝⁿ`. -/
theorem oneChart {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (p : ℕ) [Fact p.Prime] [AddAction ℤ_[p] M]
    [ContinuousVAdd ℤ_[p] M] [FaithfulVAdd ℤ_[p] M] :
    ∃ O : Set (EuclideanSpace ℝ (Fin n)), IsOpen O ∧ IsConnected O ∧
      ∃ (_ : AddAction ℤ_[p] O), ContinuousVAdd ℤ_[p] O ∧ FaithfulVAdd ℤ_[p] O := by
  sorry

end HSP
