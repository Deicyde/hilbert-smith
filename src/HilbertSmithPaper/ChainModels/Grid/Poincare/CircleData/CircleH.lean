import Mathlib
import HilbertSmithPaper.ChainModels.Grid.CubicalTorusGrid
import HilbertSmithPaper.LTheory.Base.Complexes.DualComplex
import HilbertSmithPaper.LTheory.Base.Complexes.StructureComplex

/-!
# The circle homotopy element

For the circle complex `S=S_k`, the element `H\in M(S)_2` of the structure complex given by `H(e_w^*)=e_w` and `H([w]^*)=0`: its component `(S_1)^*\to S_1` is the identity matrix and its other components are zero.
-/

open CategoryTheory

namespace HSP.ChainModels

open FreeQ DualCat

variable (k : ℕ)

/-- The element `H ∈ M(S_k)_2`: `H(e_w^*) = e_w`, `H([w]^*) = 0`. -/
def circleH : (StructureCx (circleComplex k)).X 2 :=
  fun x => ofMatrix (Matrix.of fun a b =>
    if x.1.1 = 1 then (if (a : ℕ) = b then 1 else 0) else 0)

end HSP.ChainModels
