import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Cubical.CircleComplex

/-!
# Grid cubes

A cube `c = b_1 ⊗ ⋯ ⊗ b_n` of the cubical torus grid is a choice of a cell `b_j = (w_j, j ∈ S)` of
`S_k` for each coordinate. Its dimension is `|S|`, the number of its edge coordinates.

## Encoding

`GridCube k n` (the declaration of the article) is `Fin n → Fin k × Bool`; `GridCube.dim c`
counts the coordinates `j` with `(c j).2`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.ChainModels

open FreeQ

/-- A *cube* `c = (w, S)` of the grid: for each coordinate `j` the cell `b_j = (w_j, j ∈ S)` of
`S_k`. -/
abbrev GridCube (k n : ℕ) : Type := Fin n → Fin k × Bool

/-- The dimension `|S|` of a cube: the number of its edge coordinates. -/
private def GridCube.dim {k n : ℕ} (c : GridCube k n) : ℕ :=
  ∑ j, if (c j).2 then 1 else 0

end HSP.ChainModels
