import Mathlib

/-!
# `p`-adic exclusion with boundary

As `HSP.padicExclusion`, for a connected Hausdorff space `M` charted on the half-space
`{x ∈ ℝⁿ | x 0 ≥ 0}` (Mathlib's `EuclideanHalfSpace n`, defined for `n ≥ 1`), with no
countability assumption. Mathlib does not count an `ℝⁿ`-charted space as half-space-charted, so
this is a separate declaration.

The statement is in place; its proof is still `sorry`.
-/

namespace HSP

/-- **`p`-adic exclusion with boundary.** For `n ≥ 1`, no jointly continuous action of `ℤ_[p]`
on a connected Hausdorff space charted on the half-space in `ℝⁿ` is faithful. -/
theorem padicExclusion_boundary {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M] [T2Space M]
    [ConnectedSpace M] [ChartedSpace (EuclideanHalfSpace n) M] (p : ℕ) [Fact p.Prime]
    [AddAction ℤ_[p] M] [ContinuousVAdd ℤ_[p] M] : ¬ FaithfulVAdd ℤ_[p] M := by
  sorry

end HSP
