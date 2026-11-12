import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Model.ChainModelLabel

/-!
# Torus labels of dual cells

The dual cell `a^*` of `(D_i^{N-*})_r = ((D_i)_{N-r})^*` carries the torus label of `a`, `N = n + 4`.

## Encoding

`chainModelDualLabel A i r a` (the declaration of the article) is `chainModelLabel A i (N - r) a`.
-/

open CategoryTheory

namespace HSP.ChainModels

open FreeQ

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The torus label of the dual cell `a^*` of `(D_i^{N-*})_r = ((D_i)_{N-r})^*`: the label of
`a`, `N = n + 4`. -/
noncomputable def chainModelDualLabel (A : LocalDatum p n D ρplus) (i : ℕ) (r : ℤ)
    (a : Fin ((chainModel A i).X ((n + 4 : ℕ) - r)).dim) : Torus n :=
  chainModelLabel A i ((n + 4 : ℕ) - r) a

end HSP.ChainModels
