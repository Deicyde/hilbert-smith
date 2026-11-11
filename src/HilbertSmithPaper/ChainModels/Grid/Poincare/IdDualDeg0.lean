import Mathlib
import HilbertSmithPaper.ChainModels.Grid.BasedComplexTensor

/-!
# The identity of a dual complex as a map of degree zero
-/

open CategoryTheory

namespace HSP.ChainModels

open FreeQ DualCat

/-- The identity of a dual complex `C^{m-*}`, as a map of degree `0`. -/
def idDualDeg0 (C : ChainComplex FreeQ ℤ) (m r : ℤ) : dual (C.X (m - r)) ⟶ dual (C.X (m - (r + 0))) :=
  eqToHom (by rw [add_zero])

end HSP.ChainModels
