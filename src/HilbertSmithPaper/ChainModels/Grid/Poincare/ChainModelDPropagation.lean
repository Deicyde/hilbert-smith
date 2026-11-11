import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Model.ChainModel
import HilbertSmithPaper.ChainModels.Grid.Model.ChainModelLabel
import HilbertSmithPaper.Categories.Asymptotic.Propagation

/-!
# Propagation of the differential of the chain model

With cells of the chain model `D_i` labelled at the centers of their cubes, the differential has
`d_∞`-propagation at most `h_i / 2 = 2 / k_i`: the cells occurring in `d(c ⊗ e)` are `c' ⊗ e` with
`c'` a face of `c`, whose center differs from that of `c` by `2 / k_i` in one coordinate.

## Encoding

`chainModel_d_propagation` (the declaration of the article) bounds the propagation of every
component `d r s` of the differential (it is `0` unless `s = r - 1`), with the torus labels
`chainModelLabel`.
-/

namespace HSP.ChainModels

open FreeQ

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- **Propagation of the differential of the chain model.** Every component of the differential
of `D_i` has propagation at most `h_i / 2 = 2 / k_i` for the torus labels. -/
theorem chainModel_d_propagation (A : LocalDatum p n D ρplus) (i : ℕ) (r s : ℤ) :
    (prop (chainModelLabel A i r) (chainModelLabel A i s)
      (toMatrix ((chainModel A i).d r s)) : ℝ) ≤ 2 / meshSequence A i := by
  sorry

end HSP.ChainModels
