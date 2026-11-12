import Mathlib
import HilbertSmithPaper.ChainModels.Grid.BasedComplexTensor

/-!
# Composites through a zero space vanish

If `Y` has dimension `0`, then `f ≫ g = 0` for `f : X ⟶ Y` and `g : Y ⟶ Z`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Kronecker

namespace HSP.ChainModels

open FreeQ DualCat

lemma comp_eq_zero_of_dim {X Y Z : FreeQ} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Y.dim = 0) :
    f ≫ g = 0 :=
  Matrix.ext fun i j => by
    change (toMatrix g * toMatrix f) i j = 0
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun c _ => (Fin.cast h c).elim0

end HSP.ChainModels
