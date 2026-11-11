import Mathlib
import HilbertSmithPaper.LTheory.Base.Pairs.SymmetricPoincareComplex
import HilbertSmithPaper.LTheory.Localization.Products.SymmetricLine

/-!
# The line is Poincaré

The duality map `λ_♮ : Λ^{1-*} ⟶ Λ` of the symmetric line is a chain homotopy equivalence in
`C_ℤ(ℚ)`, so `(Λ, λ)` is a strict `1`-dimensional symmetric Poincaré complex.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

/-- **The line is Poincaré**: `λ_♮ : Λ^{1-*} ⟶ Λ` is a chain homotopy equivalence. -/
theorem symLine_poincare :
    ∃ e : HomotopyEquiv (dualCx symLine 1) symLine,
      e.hom = StructureCx.toHom symLine.str symLine.str_cycle := by
  sorry

namespace symLine

/-- `Λ_r` is a zero object for `r` outside `{0, 1}`. -/
lemma isZero_X {r : ℤ} (hr : ¬(r = 0 ∨ r = 1)) : IsZero (symLine.X r) := by
  have hd : SymLine.dim r = 0 := by simp [SymLine.dim, hr]
  refine ⟨fun Y => ⟨⟨0⟩, fun f => Bounded.hom_ext fun m n => ?_⟩,
    fun Y => ⟨⟨0⟩, fun f => Bounded.hom_ext fun m n => ?_⟩⟩
  · refine Matrix.ext fun i j => ?_
    have : IsEmpty (Fin (SymLine.dim r)) := by rw [hd]; infer_instance
    exact isEmptyElim (show Fin (SymLine.dim r) from j)
  · refine Matrix.ext fun i j => ?_
    have : IsEmpty (Fin (SymLine.dim r)) := by rw [hd]; infer_instance
    exact isEmptyElim (show Fin (SymLine.dim r) from i)

/-- `(Λ, λ)` as a strict `1`-dimensional symmetric Poincaré complex. -/
noncomputable def poincare : SymPoincare (Bounded FreeQ) 1 where
  C := symLine
  φ := str
  bounded r hr := isZero_X (by omega)
  cycle := str_cycle
  symmetric := str_T
  poincare := symLine_poincare

end symLine

end HSP
