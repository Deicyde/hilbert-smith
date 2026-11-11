import HilbertSmithPaper.Proofs.IntrinsicInterior

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

/-- For a chart `φ` of `M` on the half-space, the points that `φ` maps into the open half-space
`{z | 0 < z 0}` form the domain of a homeomorphism onto an open subset of `ℝⁿ`, namely `φ`
followed by the inclusion of the half-space into `ℝⁿ`. -/
private noncomputable def posChart {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
    (φ : OpenPartialHomeomorph M (EuclideanHalfSpace n)) :
    OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) where
  toFun x := (𝓡∂ n) (φ x)
  invFun y := φ.symm ((𝓡∂ n).symm y)
  source := φ.source ∩ φ ⁻¹' {z | 0 < z.1 0}
  target := {y | 0 < y 0} ∩ (𝓡∂ n).symm ⁻¹' φ.target
  map_source' x hx := ⟨hx.2, by
    simpa only [Set.mem_preimage, ModelWithCorners.left_inv] using φ.map_source hx.1⟩
  map_target' y hy := by
    have hy0 : (0 : ℝ) ≤ y 0 := le_of_lt hy.1
    refine ⟨φ.map_target hy.2, ?_⟩
    show 0 < (φ (φ.symm ((𝓡∂ n).symm y))).1 0
    rw [φ.right_inv hy.2, modelWithCornersEuclideanHalfSpace_symm_apply_of_le hy0]
    exact hy.1
  left_inv' x hx := by
    show φ.symm ((𝓡∂ n).symm ((𝓡∂ n) (φ x))) = x
    rw [ModelWithCorners.left_inv, φ.left_inv hx.1]
  right_inv' y hy := by
    have hy0 : (0 : ℝ) ≤ y 0 := le_of_lt hy.1
    show (𝓡∂ n) (φ (φ.symm ((𝓡∂ n).symm y))) = y
    rw [φ.right_inv hy.2, modelWithCornersEuclideanHalfSpace_symm_apply_of_le hy0]
    rfl
  open_source := φ.isOpen_inter_preimage
    (isOpen_lt continuous_const ((PiLp.continuous_apply 2 _ 0).comp continuous_subtype_val))
  open_target := (isOpen_lt continuous_const (PiLp.continuous_apply 2 _ 0)).inter
    (φ.open_target.preimage (𝓡∂ n).continuous_symm)
  continuousOn_toFun :=
    (𝓡∂ n).continuous.comp_continuousOn (φ.continuousOn.mono Set.inter_subset_left)
  continuousOn_invFun :=
    φ.continuousOn_symm.comp (𝓡∂ n).continuous_symm.continuousOn fun _ hy => hy.2

/-- A point that a half-space chart maps into the open half-space is intrinsically interior. -/
private theorem mem_intrinsicInterior_of_pos {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
    (φ : OpenPartialHomeomorph M (EuclideanHalfSpace n)) {x : M} (hx : x ∈ φ.source)
    (hpos : 0 < (φ x).1 0) : x ∈ intrinsicInterior n M :=
  ⟨posChart φ, hx, hpos⟩

/-- The open half-space is dense in the half-space. -/
private theorem dense_pos_halfSpace {n : ℕ} [NeZero n] :
    Dense {z : EuclideanHalfSpace n | 0 < z.1 0} := by
  intro z
  refine closure_subtype.2 (closure_mono ?_ ((𝓡∂ n).range_subset_closure_interior ⟨z, rfl⟩))
  rw [interior_range_modelWithCornersEuclideanHalfSpace]
  intro y hy
  exact ⟨⟨y, le_of_lt hy⟩, hy, rfl⟩

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
