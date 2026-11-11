import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Cubical.GridCube

/-!
# The center of a grid cube

The center `x_c ∈ 𝕋ⁿ` of a cube `c = (w, S)` has coordinates `4w_j/k`, plus `2/k` if `j ∈ S`.

## Encoding

`GridCube.center c` is the declaration of the article.
-/

namespace HSP.ChainModels

/-- The center `x_c` of a cube: `4w_j/k`, plus `2/k` in the edge coordinates. -/
noncomputable def GridCube.center {k n : ℕ} (c : GridCube k n) : Torus n :=
  fun j => ((4 * ((c j).1 : ℕ) + if (c j).2 then 2 else 0) / k : ℝ)

end HSP.ChainModels
