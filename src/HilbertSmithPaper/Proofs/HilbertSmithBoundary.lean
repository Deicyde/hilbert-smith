import Mathlib

/-!
# Hilbert–Smith with boundary

As `HSP.hilbertSmith`, for a connected Hausdorff space `M` charted on the half-space
`{x ∈ ℝⁿ | x 0 ≥ 0}` (Mathlib's `EuclideanHalfSpace n`, defined for `n ≥ 1`). Neither `M` nor
`G` is assumed second countable, and `G` is not assumed Hausdorff.

The statement is in place; its proof is still `sorry`.
-/

open scoped ContDiff Manifold

namespace HSP

universe u v

/-- **Hilbert–Smith with boundary.** A locally compact topological group acting jointly
continuously and faithfully on a connected Hausdorff space charted on the half-space in `ℝⁿ`,
`n ≥ 1`, carries, for some `d`, an atlas of charts onto open subsets of `ℝ^d` making it a `C^∞`
Lie group. -/
theorem hilbertSmith_boundary (n : ℕ) [NeZero n] (M : Type u) [TopologicalSpace M] [T2Space M]
    [ConnectedSpace M] [ChartedSpace (EuclideanHalfSpace n) M] (G : Type v) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [MulAction G M]
    [ContinuousSMul G M] [FaithfulSMul G M] :
    ∃ (d : ℕ) (_ : ChartedSpace (EuclideanSpace ℝ (Fin d)) G), LieGroup (𝓡 d) ∞ G := by
  sorry

end HSP
