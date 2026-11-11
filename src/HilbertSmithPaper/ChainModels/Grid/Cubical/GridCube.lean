import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Cubical.CircleComplex

/-!
# Grid cubes

A cube `c = b_1 ⊗ ⋯ ⊗ b_n` of the cubical torus grid is a choice of a cell `b_j = (w_j, j ∈ S)` of
`S_k` for each coordinate.

## Encoding

`GridCube k n` (the declaration of the article) is `Fin n → Fin k × Bool`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.ChainModels

open FreeQ

/-- A *cube* `c = (w, S)` of the grid: for each coordinate `j` the cell `b_j = (w_j, j ∈ S)` of
`S_k`. -/
abbrev GridCube (k n : ℕ) : Type := Fin n → Fin k × Bool

end HSP.ChainModels
