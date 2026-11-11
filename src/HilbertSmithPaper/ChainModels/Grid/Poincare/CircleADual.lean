import Mathlib
import HilbertSmithPaper.ChainModels.Grid.CircleDuality
import HilbertSmithPaper.ChainModels.Grid.Cubical.CircleComplex

/-!
# The degree-zero map `A' = b φ^s` of the dual circle
-/

open CategoryTheory

namespace HSP.ChainModels

open FreeQ DualCat

/-- `A' = b φ^s` on `S_k^{1-*}`, as a map of degree `0`. -/
def circleA' (k : ℕ) (r : ℤ) :
    dual ((circleComplex k).X (1 - r)) ⟶ dual ((circleComplex k).X (1 - (r + 0))) :=
  circlePhiSym k ⟨(r, 1 - r), by ring⟩ ≫ circleB k r ≫
    eqToHom (by rw [add_zero])

end HSP.ChainModels
