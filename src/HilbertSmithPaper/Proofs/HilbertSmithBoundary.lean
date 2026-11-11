import HilbertSmithPaper.Proofs.HilbertSmith
import HilbertSmithPaper.Proofs.IntrinsicInterior
import HilbertSmithPaper.Proofs.IntrinsicInteriorCharted
import HilbertSmithPaper.Proofs.IntrinsicInteriorConnected
import HilbertSmithPaper.Proofs.InteriorAction
import HilbertSmithPaper.Proofs.InteriorActionContinuous
import HilbertSmithPaper.Proofs.InteriorActionFaithful

/-!
# Hilbert–Smith with boundary

As `HSP.hilbertSmith`, for a connected Hausdorff space `M` charted on the half-space
`{x ∈ ℝⁿ | x 0 ≥ 0}` (Mathlib's `EuclideanHalfSpace n`, defined for `n ≥ 1`). Neither `M` nor
`G` is assumed second countable, and `G` is not assumed Hausdorff.

Proof: the intrinsic interior `M°ₙ` is connected and charted on `ℝⁿ`, and `G` acts on it jointly
continuously and faithfully; apply `HSP.hilbertSmith` to `M°ₙ`.
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
  have : ConnectedSpace (intrinsicInterior n M) :=
    isConnected_iff_connectedSpace.1 isConnected_intrinsicInterior
  have := faithfulSMul_intrinsicInterior (n := n) (G := G) (M := M)
  exact hilbertSmith n (intrinsicInterior n M) G

end HSP
