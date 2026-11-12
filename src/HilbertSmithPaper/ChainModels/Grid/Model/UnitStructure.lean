import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Cubical.UnitComplex
import HilbertSmithPaper.LTheory.Base.Complexes.StructureComplex

/-!
# The structure of the unit complex

The structure `𝟙 ∈ M(𝟙)_0` of the unit complex: the identity of `ℚ` in degree `0`.

## Encoding

`unitStructure` (the declaration of the article).
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.ChainModels

open FreeQ DualCat

/-- The structure `𝟙 ∈ M(𝟙)_0` of the unit complex: the identity of `ℚ` in degree `0`. -/
def unitStructure : (StructureCx unitComplex).X 0 :=
  fun _ => ofMatrix (Matrix.of fun _ _ => 1)

end HSP.ChainModels
