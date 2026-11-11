import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Cp2.Cp2Complex
import HilbertSmithPaper.LTheory.Base.Complexes.DualComplex

/-!
# The inverse of the structure of `CP²`

The chain map `b_P : P → P^{4-*}`, `e_{4-r} ↦ e_r^*`.

## Encoding

`cp2Inverse` (the declaration of the article) has all-ones components; it commutes with the zero
differentials.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.ChainModels

open FreeQ DualCat

/-- The inverse `b_P : P → P^{4-*}` of `φ_P`, `e_{4-r} ↦ e_r^*`. -/
def cp2Inverse : cp2Complex ⟶ dualCx cp2Complex 4 where
  f _ := ofMatrix (Matrix.of fun _ _ => 1)
  comm' i j _ := by
    simp only [cp2Complex_d, zero_comp, dualHom_zero, smul_zero, comp_zero]

end HSP.ChainModels
