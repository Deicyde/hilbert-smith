import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Cp2.Cp2Complex

/-!
# Fundamental cycle of `CP²`

The fundamental cycle `e_4 ∈ P_4`.

## Encoding

`cp2Fundamental` (the declaration of the article) is a column, a morphism from `ℚ = ⟨1⟩`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.ChainModels

open FreeQ DualCat

/-- The fundamental cycle `e_4`, as a column. -/
def cp2Fundamental : (⟨1⟩ : FreeQ) ⟶ cp2Complex.X 4 :=
  ofMatrix (Matrix.of fun _ _ => 1)

end HSP.ChainModels
