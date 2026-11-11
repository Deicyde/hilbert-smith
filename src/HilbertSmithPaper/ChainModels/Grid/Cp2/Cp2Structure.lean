import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Cp2.Cp2Complex
import HilbertSmithPaper.LTheory.Base.Complexes.StructureComplex

/-!
# The structure of `CP²`

The structure `φ_P : P^{4-*} → P`, `e_r^* ↦ e_{4-r}`.

## Encoding

`cp2Structure` (the declaration of the article) is the element of `M(P)_4` whose every component
`φ_{p,q} : (P_q)^* → P_p` (`p + q = 4`) is the all-ones matrix: the `1 × 1` matrix `1` when
`p, q ∈ {0, 2, 4}`, and the empty matrix otherwise.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.ChainModels

open FreeQ DualCat

/-- The structure `φ_P`: `φ_{p,q} : (P_q)^* → P_p` sends `e_q^*` to `e_p` (`p + q = 4`). -/
def cp2Structure : (StructureCx cp2Complex).X 4 :=
  fun _ => ofMatrix (Matrix.of fun _ _ => 1)

end HSP.ChainModels
