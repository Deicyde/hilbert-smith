import Mathlib

/-!
# The open half-space is dense in the half-space

The range `{x | x 0 ≥ 0}` of the model with corners `𝓡∂ n` lies in the closure of its interior
`{x | x 0 > 0}` (Mathlib: `ModelWithCorners.range_subset_closure_interior`, from convexity with
nonempty interior), and closure in the subtype `EuclideanHalfSpace n` is the trace of closure in
`ℝⁿ` (`closure_subtype`).
-/

open scoped Manifold

namespace HSP

/-- For `n ≥ 1`, the open half-space `{x | x 0 > 0}` is dense in the half-space
`{x ∈ ℝⁿ | x 0 ≥ 0}`. -/
theorem dense_pos_halfSpace {n : ℕ} [NeZero n] :
    Dense {z : EuclideanHalfSpace n | 0 < z.1 0} := by
  intro z
  refine closure_subtype.2 (closure_mono ?_ ((𝓡∂ n).range_subset_closure_interior ⟨z, rfl⟩))
  rw [interior_range_modelWithCornersEuclideanHalfSpace]
  intro y hy
  exact ⟨⟨y, le_of_lt hy⟩, hy, rfl⟩

end HSP
