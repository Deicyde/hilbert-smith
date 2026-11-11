import Mathlib
import HilbertSmithPaper.ChainModels.Grid.ChainModelDuality
import HilbertSmithPaper.ChainModels.Grid.Cubical.CubicalTorusGrid
import HilbertSmithPaper.ChainModels.Grid.Cubical.CircleDimNeg
import HilbertSmithPaper.ChainModels.Grid.Cubical.CircleComplex
import HilbertSmithPaper.ChainModels.Grid.Model.UnitStructure

/-!
# The unsymmetrized grid structure

`φ^u_n = (⋯(𝟙 ⊗ φ) ⊗ ⋯) ⊗ φ ∈ M(C(k))_n`.
-/

open CategoryTheory

namespace HSP.ChainModels

open FreeQ DualCat

/-- The iterated unsymmetrized structure `(⋯(φ ⊗ φ) ⊗ ⋯) ⊗ φ ∈ M(C(k))_n`. -/
noncomputable def gridStructureU (k : ℕ) : ∀ n : ℕ, (StructureCx (gridComplex k n)).X (n : ℤ)
  | 0 => unitStructure
  | n + 1 => basedStrProd (gridComplex k n) (circleComplex k) (circleComplex_dim_neg k) n 1
      ((n + 1 : ℕ) : ℤ) (by push_cast; ring) (gridStructureU k n) (circlePhi k)

end HSP.ChainModels
