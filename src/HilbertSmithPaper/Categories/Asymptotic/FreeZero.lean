import Mathlib
import HilbertSmithPaper.Categories.Asymptotic.FreeCategory

/-!
# Objects of rank zero are zero

An object `n` of `Free(ℚ[G])` with `n = 0` is a zero object (`HSP.FreeCat.isZero_of_n_eq_zero`):
its basis `G × Fin 0` is empty, so every matrix to or from it is the empty matrix.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

variable {G : Type} [AddGroup G] [Fintype G] [DecidableEq G]

/-- An object `n` with `n = 0` is a zero object. -/
theorem FreeCat.isZero_of_n_eq_zero (Y : FreeCat G) (h : Y.n = 0) : IsZero Y := by
  obtain ⟨n⟩ := Y
  cases h
  exact ⟨fun Y => ⟨⟨⟨0⟩, fun f => FreeCat.hom_ext (Matrix.ext fun _ b => b.2.elim0)⟩⟩,
    fun Y => ⟨⟨⟨0⟩, fun f => FreeCat.hom_ext (Matrix.ext fun a _ => a.2.elim0)⟩⟩⟩

end HSP
