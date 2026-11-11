import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Model.UnitStructure
import HilbertSmithPaper.ChainModels.Grid.Cubical.CubicalTorusGrid
import HilbertSmithPaper.ChainModels.Grid.Cubical.CircleDimNeg
import HilbertSmithPaper.ChainModels.Grid.Poincare.CircleData.CirclePhiSym
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.BasedStrProd

/-!
# The structure of the grid complex

The iterated structure `(⋯(φ^s ⊗ φ^s) ⊗ ⋯) ⊗ φ^s ∈ M(C(k))_n` of the grid complex, built from the
symmetric circle structure `φ^s` by the product of structures in explicit bases, starting from the
structure of the unit complex.

## Encoding

`gridStructure k n` (the declaration of the article), by recursion on `n`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.ChainModels

open FreeQ DualCat

/-- The iterated structure `(⋯(φ^s ⊗ φ^s) ⊗ ⋯) ⊗ φ^s ∈ M(C(k))_n` of the grid complex. -/
noncomputable def gridStructure (k : ℕ) : ∀ n : ℕ, (StructureCx (gridComplex k n)).X (n : ℤ)
  | 0 => unitStructure
  | n + 1 => basedStrProd (gridComplex k n) (circleComplex k) (circleComplex_dim_neg k) n 1
      ((n + 1 : ℕ) : ℤ) (by push_cast; ring) (gridStructure k n) (circlePhiSym k)

end HSP.ChainModels
