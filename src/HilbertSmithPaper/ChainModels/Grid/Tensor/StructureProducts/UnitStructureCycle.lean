import Mathlib
import HilbertSmithPaper.ChainModels.Grid.ChainModelDuality

/-!
# The unit structure is a cycle

`∂𝟙 = 0` for the structure `𝟙 ∈ M(𝟙)_0` of the unit complex, whose differential vanishes.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.ChainModels

open FreeQ DualCat

private lemma unitComplex_d (i j : ℤ) : unitComplex.d i j = 0 := by
  by_cases h : i = j + 1
  · subst h
    exact ChainComplex.of_d unitComplex.X (fun _ => 0) j
  · exact unitComplex.shape i j (by simp only [ComplexShape.down_Rel]; omega)

/-- *The unit structure is a cycle*: `∂𝟙 = 0`. -/
lemma unitStructure_cycle : (StructureCx unitComplex).d 0 (0 - 1) unitStructure = 0 := by
  funext ⟨⟨a, b⟩, h⟩
  rw [StructureCx.d_apply unitComplex 0 (0 - 1) unitStructure a b h (0 - b) (0 - a) (by omega)
    (by omega)]
  simp only [unitComplex_d, comp_zero, dualHom_zero, zero_comp, smul_zero, add_zero]
  rfl

end HSP.ChainModels
