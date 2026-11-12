import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Cubical.CubicalTorusGrid
import HilbertSmithPaper.ChainModels.Grid.Cubical.CircleAug

/-!
# Augmentation of the grid complex

The augmentation `ε^{⊗n} : C(k)_0 → ℚ`: on the unique summand `C(k)_0 ⊠ S_{k,0}` of
`(C(k) ⊗ S_k)_0`, the Kronecker product of the augmentations.

## Encoding

`gridAug k n` (the declaration of the article), by recursion on `n`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.ChainModels

open FreeQ

/-- The augmentation `ε^{⊗n} : C(k)_0 → ℚ`: on the unique summand `C(k)_0 ⊠ S_{k,0}` of
`(C(k) ⊗ S_k)_0`, the Kronecker product of the augmentations. -/
noncomputable def gridAug (k : ℕ) : ∀ n : ℕ, (gridComplex k n).X 0 ⟶ (⟨1⟩ : FreeQ)
  | 0 => ofMatrix (Matrix.of fun _ _ => 1)
  | n + 1 => blockProj _ (0 : Fin 1) ≫ basedKron (gridAug k n) (circleAug k)

end HSP.ChainModels
