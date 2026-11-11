import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Cubical.GridCube
import HilbertSmithPaper.ChainModels.Grid.Cubical.CubicalTorusGrid
import HilbertSmithPaper.ChainModels.Grid.Cubical.GridCell
import HilbertSmithPaper.ChainModels.Grid.Cubical.GridFundamental
import HilbertSmithPaper.ChainModels.Grid.MeshSequence
import HilbertSmithPaper.ChainModels.Grid.BasedComplexTensor
import HilbertSmithPaper.LTheory.Localization.Products.BasedTensor
import HilbertSmithPaper.ChainModels.Grid.Cp2.Cp2DimNeg
import HilbertSmithPaper.ChainModels.Grid.Cp2.Cp2Fundamental
import HilbertSmithPaper.ChainModels.Grid.Cp2.Cp2Complex

/-!
# Chain model

`D_i = C(k_i) ⊗ P`, the tensor product of based complexes of the grid complex for the mesh
sequence `k_i` and the cells of `CP²`, with basis cells `c ⊗ e_r`; a cell and its dual carry the
torus label `x_c`, the center of the cube `c`. The fundamental cycle is `z_i = z(k_i) ⊗ e_4`.

## Encoding

* `chainModel A i` (the declaration of the article) is `basedComplexTensor (gridComplex k_i n) P`,
  with `k_i = meshSequence A i` for the local datum `A` in dimension `n`.
* `chainModelCube A i r a` is the cube `c` of the basis vector `a` of `(D_i)_r = ⨁_p C(k_i)_p ⊠
  P_{r-p}`, read off through the enumeration of the tensor product, and `chainModelLabel` its center
  `x_c`. The dual cell of `(D_i^{N-*})_r = ((D_i)_{N-r})^*` with the same index carries the same
  label (`chainModelDualLabel`).
* `chainModelFundamental A i` is the column `z(k_i) ⊗ e_4` in degree `n + 4`, in the summand
  `C(k_i)_n ⊠ P_4`.
-/

open CategoryTheory

namespace HSP.ChainModels

open FreeQ

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The *chain model* `D_i = C(k_i) ⊗ P`. -/
noncomputable def chainModel (A : LocalDatum p n D ρplus) (i : ℕ) : ChainComplex FreeQ ℤ :=
  basedComplexTensor (gridComplex (meshSequence A i) n) cp2Complex cp2Complex_dim_neg

/-- The cube `c` of the basis cell `c ⊗ e_{r-p}` of `(D_i)_r`. -/
noncomputable def chainModelCube (A : LocalDatum p n D ρplus) (i : ℕ) (r : ℤ)
    (a : Fin ((chainModel A i).X r).dim) : GridCube (meshSequence A i) n :=
  let s := finSigmaFinEquiv.symm a
  gridCell (meshSequence A i) n ((s.1 : ℕ) : ℤ) (finProdFinEquiv.symm s.2).1

/-- The torus label `x_c` of the basis cell `c ⊗ e_{r-p}` of `(D_i)_r`. -/
noncomputable def chainModelLabel (A : LocalDatum p n D ρplus) (i : ℕ) (r : ℤ)
    (a : Fin ((chainModel A i).X r).dim) : Torus n :=
  (chainModelCube A i r a).center

/-- The torus label of the dual cell `a^*` of `(D_i^{N-*})_r = ((D_i)_{N-r})^*`: the label of
`a`, `N = n + 4`. -/
noncomputable def chainModelDualLabel (A : LocalDatum p n D ρplus) (i : ℕ) (r : ℤ)
    (a : Fin ((chainModel A i).X ((n + 4 : ℕ) - r)).dim) : Torus n :=
  chainModelLabel A i ((n + 4 : ℕ) - r) a

/-- The fundamental cycle `z_i = z(k_i) ⊗ e_4 ∈ (D_i)_{n+4}`, as a column. -/
noncomputable def chainModelFundamental (A : LocalDatum p n D ρplus) (i : ℕ) :
    (⟨1⟩ : FreeQ) ⟶ (chainModel A i).X ((n + 4 : ℕ) : ℤ) :=
  basedKron (gridFundamental (meshSequence A i) n)
      (cp2Fundamental ≫ eqToHom (congrArg cp2Complex.X (by push_cast; ring))) ≫
    blockInc (tensorSummandDim (gridComplex (meshSequence A i) n) cp2Complex ((n + 4 : ℕ) : ℤ))
      ⟨n, by omega⟩

end HSP.ChainModels
