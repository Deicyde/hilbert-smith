import Mathlib
import HilbertSmithPaper.ChainModels.Grid.CircleDuality
import HilbertSmithPaper.ChainModels.Grid.Cubical.CircleComplex

/-!
# The degree-zero map `A = φ^s b` of the circle
-/

open CategoryTheory

namespace HSP.ChainModels

open FreeQ DualCat

/-- `A = φ^s b` on `S_k`, as a map of degree `0`. -/
def circleA (k : ℕ) (r : ℤ) : (circleComplex k).X r ⟶ (circleComplex k).X (r + 0) :=
  circleB k r ≫ circlePhiSym k ⟨(r, 1 - r), by ring⟩ ≫
    eqToHom (congrArg (circleComplex k).X (add_zero r).symm)

end HSP.ChainModels
