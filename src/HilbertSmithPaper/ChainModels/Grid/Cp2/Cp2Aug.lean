import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Cp2.Cp2Complex

/-!
# Augmentation of `CP²`

The augmentation `ε : P_0 → ℚ`, `ε e_0 = 1`.

## Encoding

`cp2Aug` (the declaration of the article).
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.ChainModels

open FreeQ DualCat

/-- The augmentation `ε e_0 = 1`. -/
def cp2Aug : cp2Complex.X 0 ⟶ (⟨1⟩ : FreeQ) :=
  ofMatrix (Matrix.of fun _ _ => 1)

end HSP.ChainModels
