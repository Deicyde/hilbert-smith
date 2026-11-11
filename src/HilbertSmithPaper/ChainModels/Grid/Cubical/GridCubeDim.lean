import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Cubical.GridCube

/-!
# The dimension of a grid cube

The dimension of a cube `c = (w, S)` is `|S|`, the number of its edge coordinates.

## Encoding

`GridCube.dim c` (the declaration of the article) counts the coordinates `j` with `(c j).2`.
-/

namespace HSP.ChainModels

/-- The dimension `|S|` of a cube: the number of its edge coordinates. -/
def GridCube.dim {k n : ℕ} (c : GridCube k n) : ℕ :=
  ∑ j, if (c j).2 then 1 else 0

end HSP.ChainModels
