import Mathlib
import HilbertSmithPaper.ChainModels.Grid.CubicalTorusGrid
import HilbertSmithPaper.LTheory.Base.Complexes.DualComplex
import HilbertSmithPaper.LTheory.Base.Complexes.StructureComplex
import HilbertSmithPaper.ChainModels.Grid.Poincare.CircleData.CircleB
import HilbertSmithPaper.ChainModels.Grid.Poincare.CircleData.CircleH

/-!
# The dual circle homotopy

For the circle complex `S=S_k`, the map `K'=\tfrac12bH` of degree `+1` on the dual complex `S^{1-*}`: in degree `r` it is `\tfrac12` times the component `(S_{1-r})^*\to S_{r+1}` of the circle homotopy element `H` followed by the circle inverse `b_{r+1}:S_{r+1}\to(S_{-r})^*`.
-/

open CategoryTheory

namespace HSP.ChainModels

open FreeQ DualCat

variable (k : ℕ)

/-- The homotopy `K' = ½ b H`, in degree `r`: `(S^{1-*})_r → (S^{1-*})_{r+1}`. -/
def circleK' (r : ℤ) :
    (dualCx (circleComplex k) 1).X r ⟶ (dualCx (circleComplex k) 1).X (r + 1) :=
  (1 / 2 : ℚ) • (circleH k ⟨(r + 1, 1 - r), by ring⟩ ≫ circleB k (r + 1))

end HSP.ChainModels
