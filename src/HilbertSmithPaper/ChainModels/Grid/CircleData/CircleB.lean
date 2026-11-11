import Mathlib
import HilbertSmithPaper.ChainModels.Grid.CubicalTorusGrid
import HilbertSmithPaper.LTheory.Base.Complexes.DualComplex
import HilbertSmithPaper.LTheory.Base.Complexes.StructureComplex

/-!
# The circle inverse

For the circle complex `S=S_k`, the map `b:S\to S^{1-*}` into the dual complex, given in degree `r` by `b(e_w)=[w+1]^*` for `r=1`, `b([w])=e_w^*` for `r=0`, and `0` in the other degrees.
-/

open CategoryTheory

namespace HSP.ChainModels

open FreeQ DualCat

variable (k : ℕ)

/-- The component `b_r : S_r → (S^{1-*})_r` of the inverse `b`: `b(e_w) = [w+1]^*`,
`b([w]) = e_w^*`. -/
def circleB (r : ℤ) : (circleComplex k).X r ⟶ (dualCx (circleComplex k) 1).X r :=
  ofMatrix (Matrix.of fun a b =>
    if r = 1 then (if (a : ℕ) = ((b : ℕ) + 1) % k then 1 else 0)
    else if r = 0 then (if (a : ℕ) = b then 1 else 0) else 0)

end HSP.ChainModels
