import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Tensor.BasedTensorHom
import HilbertSmithPaper.ChainModels.Grid.Tensor.IdDeg0
import HilbertSmithPaper.ChainModels.Grid.Poincare.CircleA
import HilbertSmithPaper.ChainModels.Grid.Cubical.CubicalTorusGrid
import HilbertSmithPaper.ChainModels.Grid.Cubical.CircleDimNeg

/-!
# The grid homotopy

`H^{(0)} = 0`, `H^{(n+1)} = H^{(n)} ⊗ A + 1 ⊗ K`.
-/

open CategoryTheory

namespace HSP.ChainModels

open FreeQ DualCat

/-- The homotopy `H^{(n)} = ∑_j 1^{⊗(j-1)} ⊗ K ⊗ A^{⊗(n-j)}` on `C(k)`, by the recursion
`H^{(n+1)} = H^{(n)} ⊗ A + 1 ⊗ K`. -/
noncomputable def gridH (k : ℕ) : ∀ (n : ℕ) (r : ℤ), (gridComplex k n).X r ⟶ (gridComplex k n).X (r + 1)
  | 0, _ => 0
  | n + 1, r =>
    basedTensorHom (circleComplex_dim_neg k) (circleComplex_dim_neg k) 1 0 (gridH k n)
        (circleA k) r ≫ eqToHom (congrArg (gridComplex k (n + 1)).X (by ring)) +
      basedTensorHom (circleComplex_dim_neg k) (circleComplex_dim_neg k) 0 1
        (idDeg0 (gridComplex k n)) (circleK k) r ≫
        eqToHom (congrArg (gridComplex k (n + 1)).X (by ring))

end HSP.ChainModels
