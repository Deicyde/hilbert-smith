import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Poincare.GridHDual
import HilbertSmithPaper.ChainModels.Grid.Cp2.Cp2DimNeg
import HilbertSmithPaper.ChainModels.Grid.ChainModel
import HilbertSmithPaper.LTheory.Base.Complexes.DualComplex
import HilbertSmithPaper.ChainModels.Grid.Cp2.Cp2Complex

/-!
# The dual homotopy of the chain model

`H'_i = Ξ^{-1}(H'^{(n)} ⊗ 1_{P^{4-*}})Ξ`.
-/

open CategoryTheory

namespace HSP.ChainModels

open FreeQ DualCat

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The homotopy `H'_i = Ξ^{-1}(H'^{(n)} ⊗ 1_{P^{4-*}})Ξ` on `D_i^{N-*}`, in degree `r`. -/
noncomputable def chainModelH' (A : LocalDatum p n D ρplus) (i : ℕ) (r : ℤ) :
    (dualCx (chainModel A i) ((n + 4 : ℕ) : ℤ)).X r ⟶
      (dualCx (chainModel A i) ((n + 4 : ℕ) : ℤ)).X (r + 1) :=
  basedDualTensorHom cp2Complex_dim_neg n 4 ((n + 4 : ℕ) : ℤ) (by push_cast; ring) 1 0
      (gridH' (meshSequence A i) n) (idDualDeg0 cp2Complex 4) r ≫
    eqToHom (congrArg (fun t => dual ((chainModel A i).X (((n + 4 : ℕ) : ℤ) - t)))
      (show r + (1 + 0) = r + 1 by ring))

end HSP.ChainModels
