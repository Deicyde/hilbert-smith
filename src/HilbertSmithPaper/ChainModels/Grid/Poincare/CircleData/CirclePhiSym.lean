import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Cubical.CircleComplex
import HilbertSmithPaper.LTheory.Base.Complexes.DualComplex
import HilbertSmithPaper.LTheory.Base.Complexes.StructureComplex
import HilbertSmithPaper.ChainModels.Grid.Poincare.CircleData.CirclePhi
import HilbertSmithPaper.ChainModels.Grid.Poincare.CircleData.CircleH

/-!
# The symmetric circle structure

For the circle complex `S=S_k`, the element `\varphi^s=\varphi+\tfrac12\partial H\in M(S)_1` of the structure complex, where `\varphi` is the circle structure, `H` the circle homotopy element and `\partial` the differential of `M(S)`.
-/

open CategoryTheory

namespace HSP.ChainModels

open FreeQ DualCat

variable (k : ℕ)

/-- The symmetric structure `φ^s = φ + ½ ∂H`. -/
def circlePhiSym : (StructureCx (circleComplex k)).X 1 :=
  circlePhi k + (1 / 2 : ℚ) • (StructureCx (circleComplex k)).d 2 1 (circleH k)

end HSP.ChainModels
