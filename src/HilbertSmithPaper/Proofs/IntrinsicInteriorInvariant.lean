import HilbertSmithPaper.Proofs.IntrinsicInterior

/-!
# The intrinsic interior is invariant

A homeomorphism `h` of `M` carries a chart `e` at `x` to the chart `h⁻¹ ≫ e` at `h x`; applied to
`h` and `h⁻¹` this gives `h '' M°ₙ = M°ₙ`.
-/

namespace HSP

/-- Every homeomorphism `h` of `M` maps the intrinsic interior onto itself:
`h '' M°ₙ = M°ₙ`. -/
theorem image_intrinsicInterior (n : ℕ) {M : Type*} [TopologicalSpace M] (h : M ≃ₜ M) :
    h '' intrinsicInterior n M = intrinsicInterior n M := by
  -- the forward inclusion for every homeomorphism
  have key : ∀ h : M ≃ₜ M, h '' intrinsicInterior n M ⊆ intrinsicInterior n M := by
    rintro h _ ⟨x, ⟨e, hx⟩, rfl⟩
    refine ⟨h.symm.toOpenPartialHomeomorph.trans e, ?_⟩
    simpa using hx
  refine (key h).antisymm fun x hx => ⟨h.symm x, key h.symm ⟨x, hx, rfl⟩, h.apply_symm_apply x⟩

end HSP
