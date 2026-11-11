import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Cubical.GridCube
import HilbertSmithPaper.ChainModels.Grid.Cubical.CellRealization

/-!
# The closed cube

The closed cube `|c| ⊆ 𝕋ⁿ` of a grid cube is the product of the realizations of its cells.

## Encoding

`GridCube.realization c` (the declaration of the article) is `Set.pi Set.univ` of the cell
realizations, in `𝕋ⁿ = Fin n → ℝ/4ℤ`.
-/

namespace HSP.ChainModels

/-- The closed cube `|c| ⊆ 𝕋ⁿ`, the product of the realizations of its cells. -/
def GridCube.realization {k n : ℕ} (c : GridCube k n) : Set (Torus n) :=
  Set.pi Set.univ fun j => cellRealization k (c j)

end HSP.ChainModels
