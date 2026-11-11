import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Cubical.CubicalTorusGrid
import HilbertSmithPaper.ChainModels.Grid.MeshSequence
import HilbertSmithPaper.ChainModels.Grid.BasedComplexTensor
import HilbertSmithPaper.LTheory.Localization.Products.BasedTensor
import HilbertSmithPaper.ChainModels.Grid.Cp2.Cp2DimNeg
import HilbertSmithPaper.ChainModels.Grid.Cp2.Cp2Complex

/-!
# Chain model

`D_i = C(k_i) ⊗ P`, the tensor product of based complexes of the grid complex for the mesh
sequence `k_i` and the cells of `CP²`, with basis cells `c ⊗ e_r`.

## Encoding

`chainModel A i` (the declaration of the article) is `basedComplexTensor (gridComplex k_i n) P`,
with `k_i = meshSequence A i` for the local datum `A` in dimension `n`.
-/

open CategoryTheory

namespace HSP.ChainModels

open FreeQ

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The *chain model* `D_i = C(k_i) ⊗ P`. -/
noncomputable def chainModel (A : LocalDatum p n D ρplus) (i : ℕ) : ChainComplex FreeQ ℤ :=
  basedComplexTensor (gridComplex (meshSequence A i) n) cp2Complex cp2Complex_dim_neg

end HSP.ChainModels
