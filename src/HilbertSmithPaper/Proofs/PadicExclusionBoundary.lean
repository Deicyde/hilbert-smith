import HilbertSmithPaper.Proofs.PadicExclusion
import HilbertSmithPaper.Proofs.IntrinsicInterior
import HilbertSmithPaper.Proofs.IntrinsicInteriorCharted
import HilbertSmithPaper.Proofs.IntrinsicInteriorConnected
import HilbertSmithPaper.Proofs.InteriorAction
import HilbertSmithPaper.Proofs.InteriorActionContinuous
import HilbertSmithPaper.Proofs.InteriorActionFaithful

/-!
# `p`-adic exclusion with boundary

As `HSP.padicExclusion`, for a connected Hausdorff space `M` charted on the half-space
`{x ∈ ℝⁿ | x 0 ≥ 0}` (Mathlib's `EuclideanHalfSpace n`, defined for `n ≥ 1`), with no
countability assumption. Mathlib does not count an `ℝⁿ`-charted space as half-space-charted, so
this is a separate declaration.

Proof: the intrinsic interior `M°ₙ` is connected, Hausdorff as a subspace and charted on `ℝⁿ`;
the action restricts to a jointly continuous action on it, which is faithful; this contradicts
`HSP.padicExclusion` for `M°ₙ`.
-/

namespace HSP

/-- **`p`-adic exclusion with boundary.** For `n ≥ 1`, no jointly continuous action of `ℤ_[p]`
on a connected Hausdorff space charted on the half-space in `ℝⁿ` is faithful. -/
theorem padicExclusion_boundary {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M] [T2Space M]
    [ConnectedSpace M] [ChartedSpace (EuclideanHalfSpace n) M] (p : ℕ) [Fact p.Prime]
    [AddAction ℤ_[p] M] [ContinuousVAdd ℤ_[p] M] : ¬ FaithfulVAdd ℤ_[p] M := by
  intro _
  have : ConnectedSpace (intrinsicInterior n M) :=
    isConnected_iff_connectedSpace.1 isConnected_intrinsicInterior
  exact padicExclusion (n := n) (X := intrinsicInterior n M) p
    (faithfulVAdd_intrinsicInterior (n := n) (G := ℤ_[p]) (M := M))

end HSP
