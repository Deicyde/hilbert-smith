import Mathlib
import HilbertSmithPaper.LocalData.Subgroups.FixedSets

/-!
# A point with no fixed neighbourhood

For a jointly continuous faithful action of `ℤ_[p]` on a connected `n`-manifold `M`, some point has
no neighbourhood fixed pointwise by any `H_j`.

## Encoding

An `n`-manifold is a Hausdorff space (`T2Space`) with an atlas of open partial homeomorphisms onto
open subsets of `ℝⁿ = EuclideanSpace ℝ (Fin n)` (`ChartedSpace`), with no countability assumption;
connected spaces are nonempty (`ConnectedSpace`). The action is `AddAction ℤ_[p] M` with
`ContinuousVAdd` (joint continuity) and `FaithfulVAdd`.
-/

open Topology

namespace HSP

/-- A faithful jointly continuous action of `ℤ_[p]` on a connected `n`-manifold has a point `x`
such that no `Fix_j(M)` is a neighbourhood of `x`. -/
theorem exists_good_point {p : ℕ} [Fact p.Prime] {n : ℕ} {M : Type*} [TopologicalSpace M]
    [T2Space M] [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [AddAction ℤ_[p] M] [ContinuousVAdd ℤ_[p] M] [FaithfulVAdd ℤ_[p] M] :
    ∃ x : M, ∀ j, fixSet p M j ∉ 𝓝 x := by
  sorry

end HSP
