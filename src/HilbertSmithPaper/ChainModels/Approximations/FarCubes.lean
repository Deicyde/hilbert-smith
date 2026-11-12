import Mathlib
import HilbertSmithPaper.ChainModels.Torus.Proj
import HilbertSmithPaper.ChainModels.Grid.Cubical.GridCube
import HilbertSmithPaper.ChainModels.Grid.Cubical.GridCubeRealization

/-!
# Far cubes

A cube `c` of `C(k)` is *far* if its closed cube `|c|` misses `B̄(0, 3/2)`; the far cubes span
the subcomplex `E(k) ⊆ C(k)`.

## Encoding

`IsFarCube c` (the declaration of the article) says the realization of `c` is disjoint from the
image in `𝕋ⁿ` of the closed Euclidean ball `B̄(0, 3/2)` under the quotient map. `E(k)` is not
built as a subcomplex: its cubes are the far basis cubes.
-/

namespace HSP.ChainModels

variable {n : ℕ}

/-- The closed cube `|c|` misses `B̄(0, 3/2) ⊆ 𝕋ⁿ`: `c` is a cube of `E(k)`. -/
def IsFarCube {k : ℕ} (c : GridCube k n) : Prop :=
  Disjoint c.realization
    (Torus.proj '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (3 / 2))

end HSP.ChainModels
