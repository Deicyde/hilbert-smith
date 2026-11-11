import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Model.ChainModelCube

/-!
# Torus labels of chain-model cells

The basis cell `c ⊗ e_{r-p}` of `(D_i)_r` carries the torus label `x_c`, the center of `c`.

## Encoding

`chainModelLabel A i r a` (the declaration of the article) is the center of `chainModelCube`.
-/

open CategoryTheory

namespace HSP.ChainModels

open FreeQ

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The torus label `x_c` of the basis cell `c ⊗ e_{r-p}` of `(D_i)_r`. -/
noncomputable def chainModelLabel (A : LocalDatum p n D ρplus) (i : ℕ) (r : ℤ)
    (a : Fin ((chainModel A i).X r).dim) : Torus n :=
  (chainModelCube A i r a).center

end HSP.ChainModels
