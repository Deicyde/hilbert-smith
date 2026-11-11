import Mathlib
import HilbertSmithPaper.ChainModels.Grid.CubicalTorusGrid
import HilbertSmithPaper.ChainModels.Grid.Realization

/-!
# Realized augmentation

The augmentation `ε : C(k)_0 → ℚ` of the cubical torus grid, on the realization of `C(k)_0`:
the linear map sending a column `z` to `ε z`.

## Encoding

`gridAugLin k n` (the declaration of the article) applies the `1 × dim` matrix of `gridAug k n`
to a column (`Matrix.mulVecLin`) and takes the single entry of the result.
-/

namespace HSP.ChainModels

open FreeQ

/-- The augmentation `ε : C(k)_0 → ℚ`, realized as a linear map on columns. -/
noncomputable def gridAugLin (k n : ℕ) : (realizeCx (gridComplex k n)).X 0 →ₗ[ℚ] ℚ :=
  (LinearMap.proj (0 : Fin 1)).comp (Matrix.mulVecLin (toMatrix (gridAug k n)))

end HSP.ChainModels
