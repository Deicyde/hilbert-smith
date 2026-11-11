import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Cubical.CircleComplex
import HilbertSmithPaper.LTheory.Base.Complexes.DualComplex
import HilbertSmithPaper.LTheory.Base.Complexes.StructureComplex

/-!
# The circle structure

For the circle complex `S=S_k`, the element `\varphi\in M(S)_1` of the structure complex given by `\varphi([w]^*)=e_{w-1}` and `\varphi(e_w^*)=[w]` for `w\in\mathbb Z/k`: its component `(S_1)^*\to S_0` is the identity matrix, its component `(S_0)^*\to S_1` has entry `1` in row `e_{w-1}` and column `[w]^*` and `0` elsewhere, and its other components are zero.
-/

open CategoryTheory

namespace HSP.ChainModels

open FreeQ DualCat

variable (k : ℕ)

/-- The structure `φ ∈ M(S_k)_1`: `φ(e_w^*) = [w]` and `φ([w]^*) = e_{w-1}`. -/
def circlePhi : (StructureCx (circleComplex k)).X 1 :=
  fun x => ofMatrix (Matrix.of fun a b =>
    if x.1.1 = 0 then (if (a : ℕ) = b then 1 else 0)
    else if x.1.1 = 1 then (if (a : ℕ) = ((b : ℕ) + k - 1) % k then 1 else 0) else 0)

end HSP.ChainModels
