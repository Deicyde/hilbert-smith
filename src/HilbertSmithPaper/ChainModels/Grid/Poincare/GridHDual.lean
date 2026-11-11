import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Tensor.BasedDualTensorHom
import HilbertSmithPaper.ChainModels.Grid.Poincare.IdDualDeg0
import HilbertSmithPaper.ChainModels.Grid.Poincare.CircleADual

/-!
# The dual grid homotopy

`H'^{(0)} = 0`, `H'^{(n+1)} = Ξ^{-1}(H'^{(n)} ⊗ A' + 1 ⊗ K')Ξ`.
-/

open CategoryTheory

namespace HSP.ChainModels

open FreeQ DualCat

/-- The homotopy `H'^{(n)} = Ξ^{-1}(∑_j 1^{⊗(j-1)} ⊗ K' ⊗ A'^{⊗(n-j)})Ξ` on `C(k)^{n-*}`. -/
noncomputable def gridH' (k : ℕ) : ∀ (n : ℕ) (r : ℤ),
    dual ((gridComplex k n).X ((n : ℤ) - r)) ⟶ dual ((gridComplex k n).X ((n : ℤ) - (r + 1)))
  | 0, _ => 0
  | n + 1, r =>
    basedDualTensorHom (circleComplex_dim_neg k) n 1 ((n + 1 : ℕ) : ℤ) (by push_cast; ring) 1 0
        (gridH' k n) (circleA' k) r ≫
        eqToHom (congrArg (fun t => dual ((gridComplex k (n + 1)).X (((n + 1 : ℕ) : ℤ) - t)))
          (show r + (1 + 0) = r + 1 by ring)) +
      basedDualTensorHom (circleComplex_dim_neg k) n 1 ((n + 1 : ℕ) : ℤ) (by push_cast; ring) 0 1
        (idDualDeg0 (gridComplex k n) n) (circleK' k) r ≫
        eqToHom (congrArg (fun t => dual ((gridComplex k (n + 1)).X (((n + 1 : ℕ) : ℤ) - t)))
          (show r + (0 + 1) = r + 1 by ring))

end HSP.ChainModels
