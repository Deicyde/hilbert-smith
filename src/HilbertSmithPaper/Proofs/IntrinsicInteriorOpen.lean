import HilbertSmithPaper.Proofs.IntrinsicInterior

/-!
# The intrinsic interior is open

Every chart domain onto an open subset of `ℝⁿ` lies in the intrinsic interior, so the
intrinsic interior is a union of open sets.
-/

namespace HSP

/-- The intrinsic interior `M°ₙ` is open in `M`. -/
theorem isOpen_intrinsicInterior (n : ℕ) (M : Type*) [TopologicalSpace M] :
    IsOpen (intrinsicInterior n M) := by
  refine isOpen_iff_forall_mem_open.2 fun x ⟨e, hx⟩ => ⟨e.source, fun y hy => ⟨e, hy⟩,
    e.open_source, hx⟩

end HSP
