import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Model.ChainModel
import HilbertSmithPaper.ChainModels.Grid.Cubical.GridCube
import HilbertSmithPaper.ChainModels.Grid.Cubical.GridCell

/-!
# The cube of a chain-model cell

The basis cell `c ⊗ e_{r-p}` of `(D_i)_r = ⨁_p C(k_i)_p ⊠ P_{r-p}` has the cube `c`.

## Encoding

`chainModelCube A i r a` (the declaration of the article) reads the cube of the basis vector `a`
off the enumeration of the tensor product.
-/

open CategoryTheory

namespace HSP.ChainModels

open FreeQ

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The cube `c` of the basis cell `c ⊗ e_{r-p}` of `(D_i)_r`. -/
noncomputable def chainModelCube (A : LocalDatum p n D ρplus) (i : ℕ) (r : ℤ)
    (a : Fin ((chainModel A i).X r).dim) : GridCube (meshSequence A i) n :=
  let s := finSigmaFinEquiv.symm a
  gridCell (meshSequence A i) n ((s.1 : ℕ) : ℤ) (finProdFinEquiv.symm s.2).1

end HSP.ChainModels
