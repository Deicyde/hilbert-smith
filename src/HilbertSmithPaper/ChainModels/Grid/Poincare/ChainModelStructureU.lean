import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Poincare.GridStructureU
import HilbertSmithPaper.ChainModels.Grid.Cp2.Cp2DimNeg
import HilbertSmithPaper.ChainModels.Grid.Model.ChainModel
import HilbertSmithPaper.ChainModels.Grid.Cubical.CubicalTorusGrid
import HilbertSmithPaper.ChainModels.Grid.Cp2.Cp2Structure
import HilbertSmithPaper.ChainModels.Grid.Cp2.Cp2Complex

/-!
# The unsymmetrized structure of the chain model

`φ_i^u = φ^u_n ⊗ φ_P ∈ M(D_i)_N`.
-/

open CategoryTheory

namespace HSP.ChainModels

open FreeQ DualCat

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The unsymmetrized structure `φ_i^u = (⋯(φ ⊗ φ) ⊗ ⋯ ⊗ φ) ⊗ φ_P ∈ M(D_i)_N`. -/
noncomputable def chainModelStructureU (A : LocalDatum p n D ρplus) (i : ℕ) :
    (StructureCx (chainModel A i)).X ((n + 4 : ℕ) : ℤ) :=
  basedStrProd (gridComplex (meshSequence A i) n) cp2Complex cp2Complex_dim_neg n 4
    ((n + 4 : ℕ) : ℤ) (by push_cast; ring) (gridStructureU (meshSequence A i) n) cp2Structure

end HSP.ChainModels
