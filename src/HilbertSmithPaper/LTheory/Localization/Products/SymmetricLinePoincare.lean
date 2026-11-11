import Mathlib
import HilbertSmithPaper.LTheory.Base.Pairs.SymmetricPoincareComplex
import HilbertSmithPaper.LTheory.Localization.Products.SymmetricLineCycle

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
      e.hom = StructureCx.toHom symLine.str symLine.str_T_and_cycle.2 := by
  sorry

end HSP
