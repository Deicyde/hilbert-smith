import HilbertSmithPaper.Proofs.IntrinsicInterior

/-!
# Points over the open half-space are interior

A chart `φ` on the half-space `{x ∈ ℝⁿ | x 0 ≥ 0}` (Mathlib's `EuclideanHalfSpace n`) is an
`OpenPartialHomeomorph M (EuclideanHalfSpace n)`. Restricted to the points it maps into the open
half-space and followed by the inclusion of the half-space into `ℝⁿ` (the model with corners
`𝓡∂ n`), it is an `OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))`: its target is
`{y | 0 < y 0} ∩ r⁻¹(φ.target)` with `r = (𝓡∂ n).symm` the continuous retraction
`y ↦ (max (y 0) 0, y 1, …)`, and its inverse is `φ.symm ∘ r`.
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

/-- For `n ≥ 1` and a homeomorphism `φ` from an open subset of `M` onto an open subset of the
half-space `{x ∈ ℝⁿ | x 0 ≥ 0}`, a point `x` of its domain with `φ(x) 0 > 0` is intrinsically
interior. -/
theorem mem_intrinsicInterior_of_pos {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
    (φ : OpenPartialHomeomorph M (EuclideanHalfSpace n)) {x : M} (hx : x ∈ φ.source)
    (hpos : 0 < (φ x).1 0) : x ∈ intrinsicInterior n M :=
  ⟨posChart φ, hx, hpos⟩

end HSP
