import HilbertSmithPaper.Proofs.IntrinsicInterior
import HilbertSmithPaper.Proofs.HalfSpaceInterior
import HilbertSmithPaper.Proofs.OpenHalfSpaceDense

/-!
# The intrinsic interior is dense

For a chart `φ` of `M` on the half-space `{x ∈ ℝⁿ | x 0 ≥ 0}` (Mathlib's `EuclideanHalfSpace n`),
the points of its domain that `φ` maps into the open half-space lie in `M°ₙ` (`φ` followed by the
inclusion into `ℝⁿ` is a homeomorphism onto an open set there). The open half-space is dense in
the half-space, and `φ⁻¹` is continuous, so these points are dense in the domain of `φ`; the
chart domains cover `M`.
-/

open scoped Manifold

namespace HSP

/-- For `n ≥ 1` and a space `M` with an atlas on the half-space `{x ∈ ℝⁿ | x 0 ≥ 0}`, the
intrinsic interior `M°ₙ` is dense in `M`. -/
theorem dense_intrinsicInterior {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M] : Dense (intrinsicInterior n M) := by
  intro x
  set φ := chartAt (EuclideanHalfSpace n) x
  have hx : x ∈ φ.source := mem_chart_source _ x
  have h1 : φ x ∈ closure (φ.target ∩ {z | 0 < z.1 0}) :=
    φ.open_target.inter_closure ⟨φ.map_source hx, dense_pos_halfSpace _⟩
  have h2 := ((φ.continuousOn_symm (φ x) (φ.map_source hx)).mono
    Set.inter_subset_left).mem_closure_image h1
  rw [φ.left_inv hx] at h2
  refine closure_mono ?_ h2
  rintro _ ⟨z, hz, rfl⟩
  exact mem_intrinsicInterior_of_pos φ (φ.map_target hz.1) (by rw [φ.right_inv hz.1]; exact hz.2)

end HSP
