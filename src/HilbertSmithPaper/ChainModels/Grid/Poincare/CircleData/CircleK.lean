import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Cubical.CircleComplex
import HilbertSmithPaper.LTheory.Base.Complexes.DualComplex
import HilbertSmithPaper.LTheory.Base.Complexes.StructureComplex
import HilbertSmithPaper.ChainModels.Grid.Poincare.CircleData.CircleB
import HilbertSmithPaper.ChainModels.Grid.Poincare.CircleData.CircleH

/-!
# The circle homotopy

For the circle complex `S=S_k`, the map `K=\tfrac12Hb` of degree `+1` on `S`: in degree `r` it is `\tfrac12` times the circle inverse `b_r:S_r\to(S_{1-r})^*` followed by the component `(S_{1-r})^*\to S_{r+1}` of the circle homotopy element `H`.
-/

open CategoryTheory

namespace HSP.ChainModels

open FreeQ DualCat

variable (k : ℕ)

/-- The homotopy `K = ½ H b`, in degree `r`: `S_r → S_{r+1}`. -/
def circleK (r : ℤ) : (circleComplex k).X r ⟶ (circleComplex k).X (r + 1) :=
  (1 / 2 : ℚ) • (circleB k r ≫ circleH k ⟨(r + 1, 1 - r), by ring⟩)

end HSP.ChainModels
