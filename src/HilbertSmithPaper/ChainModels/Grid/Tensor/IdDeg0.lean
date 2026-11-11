import Mathlib
import HilbertSmithPaper.ChainModels.Grid.BasedComplexTensor

/-!
# The identity as a map of degree `0`

The identity of a complex `C` of based vector spaces, regarded as a graded map `C_r → C_{r+0}` of
degree `0`, so that it can be tensored with other graded maps by `basedTensorHom`.

## Encoding

`idDeg0 C r` is the identity transport `C_r = C_{r+0}`.
-/

open CategoryTheory

namespace HSP.ChainModels

/-- The identity of a complex, as a map of degree `0`. -/
def idDeg0 (C : ChainComplex FreeQ ℤ) (r : ℤ) : C.X r ⟶ C.X (r + 0) :=
  eqToHom (congrArg C.X (add_zero r).symm)

end HSP.ChainModels
