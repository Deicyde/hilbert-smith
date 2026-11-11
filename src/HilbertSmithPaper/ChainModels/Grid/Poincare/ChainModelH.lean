import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Poincare.GridH
import HilbertSmithPaper.ChainModels.Grid.Cp2.Cp2DimNeg
import HilbertSmithPaper.ChainModels.Grid.ChainModel
import HilbertSmithPaper.ChainModels.Grid.Cp2.Cp2Complex

/-!
# The homotopy of the chain model

`H_i = H^{(n)} ⊗ 1_P`.
-/

open CategoryTheory

namespace HSP.ChainModels

open FreeQ DualCat

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The homotopy `H_i = H^{(n)} ⊗ 1_P` on `D_i`, in degree `r`. -/
noncomputable def chainModelH (A : LocalDatum p n D ρplus) (i : ℕ) (r : ℤ) :
    (chainModel A i).X r ⟶ (chainModel A i).X (r + 1) :=
  basedTensorHom cp2Complex_dim_neg cp2Complex_dim_neg 1 0 (gridH (meshSequence A i) n)
      (idDeg0 cp2Complex) r ≫ eqToHom (congrArg (chainModel A i).X (by ring))

end HSP.ChainModels
