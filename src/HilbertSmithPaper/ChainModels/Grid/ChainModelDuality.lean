import Mathlib
import HilbertSmithPaper.ChainModels.Grid.ChainModel
import HilbertSmithPaper.ChainModels.Grid.CircleDuality
import HilbertSmithPaper.ChainModels.Grid.Cp2Cells
import HilbertSmithPaper.LTheory.Base.Complexes.DualComplex
import HilbertSmithPaper.LTheory.Base.Complexes.StructureComplex
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.BasedStrProd
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.BasedDualProd

/-!
# Chain-model duality

The duality data of `D_i`: the structure `φ_i ∈ M(D_i)_N`, the iterated external product
`(⋯(φ^s ⊗ φ^s) ⊗ ⋯ ⊗ φ^s) ⊗ φ_P`, and the map `b_i = Ξ^{-1} ∘ (b ⊗ ⋯ ⊗ b ⊗ b_P) : D_i → D_i^{N-*}`,
`N = n + 4`.

## Encoding

* All products are computed in the explicit bases of the tensor product of based complexes, by
  `basedStrProd` (the product of structures) and `basedDualProd` (the product of duality maps
  through `Ξ^{-1}`), each with its own article.
* The iterates start from the unit complex `𝟙` (structure and map the identity of `ℚ` in degree
  `0`), as `C(k)` does; the first step multiplies by the unit with sign `+1`.
* `chainModelDuality A i` (the declaration of the article) is the pair `(φ_i, b_i)`, with `b_i`
  given by its components `(b_i)_r : (D_i)_r → (D_i^{N-*})_r`.
-/

open CategoryTheory

namespace HSP.ChainModels

open FreeQ DualCat

/-- The structure `𝟙 ∈ M(𝟙)_0` of the unit complex: the identity of `ℚ` in degree `0`. -/
def unitStructure : (StructureCx unitComplex).X 0 :=
  fun _ => ofMatrix (Matrix.of fun _ _ => 1)

/-- The map `𝟙 → 𝟙^{0-*}`: the identity of `ℚ` in degree `0`. -/
def unitDualMap (r : ℤ) : unitComplex.X r ⟶ dual (unitComplex.X (0 - r)) :=
  ofMatrix (Matrix.of fun _ _ => 1)

private lemma unitComplex_dim_neg : ∀ q < 0, (unitComplex.X q).dim = 0 := by
  intro q hq
  rcases q with q | q
  · exact absurd hq (by simp)
  · rfl

/-- The iterated structure `(⋯(φ^s ⊗ φ^s) ⊗ ⋯) ⊗ φ^s ∈ M(C(k))_n` of the grid complex. -/
noncomputable def gridStructure (k : ℕ) : ∀ n : ℕ, (StructureCx (gridComplex k n)).X (n : ℤ)
  | 0 => unitStructure
  | n + 1 => basedStrProd (gridComplex k n) (circleComplex k) (circleComplex_dim_neg k) n 1
      ((n + 1 : ℕ) : ℤ) (by push_cast; ring) (gridStructure k n) (circlePhiSym k)

/-- The iterated map `b ⊗ ⋯ ⊗ b : C(k) → C(k)^{n-*}` (through `Ξ^{-1}`), by components. -/
noncomputable def gridDualMap (k : ℕ) :
    ∀ (n : ℕ) (r : ℤ), (gridComplex k n).X r ⟶ dual ((gridComplex k n).X ((n : ℤ) - r))
  | 0 => unitDualMap
  | n + 1 => basedDualProd (gridComplex k n) (circleComplex k) (circleComplex_dim_neg k) n 1
      ((n + 1 : ℕ) : ℤ) (by push_cast; ring) (gridDualMap k n) (circleB k)

/-- The duality data of the chain model: a structure `φ` and the components `b_r` of a map
`b : D → D^{N-*}`. -/
structure ChainModelDualityData (Dc : ChainComplex FreeQ ℤ) (N : ℤ) where
  /-- The structure `φ ∈ M(D)_N`. -/
  φ : (StructureCx Dc).X N
  /-- The components `b_r : D_r → (D^{N-*})_r`. -/
  b : ∀ r, Dc.X r ⟶ (dualCx Dc N).X r

private lemma cp2Complex_dim_neg' : ∀ q < 0, (cp2Complex.X q).dim = 0 := by
  intro q hq
  rcases q with q | q
  · exact absurd hq (by simp)
  · rfl

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- *Chain-model duality*: `φ_i = (⋯(φ^s ⊗ φ^s) ⊗ ⋯ ⊗ φ^s) ⊗ φ_P ∈ M(D_i)_N` and
`b_i = Ξ^{-1} ∘ (b ⊗ ⋯ ⊗ b ⊗ b_P)`, `N = n + 4`. -/
noncomputable def chainModelDuality (A : LocalDatum p n D ρplus) (i : ℕ) :
    ChainModelDualityData (chainModel A i) ((n + 4 : ℕ) : ℤ) where
  φ := basedStrProd (gridComplex (meshSequence A i) n) cp2Complex cp2Complex_dim_neg' n 4
    ((n + 4 : ℕ) : ℤ) (by push_cast; ring) (gridStructure (meshSequence A i) n) cp2Structure
  b := basedDualProd (gridComplex (meshSequence A i) n) cp2Complex cp2Complex_dim_neg' n 4
    ((n + 4 : ℕ) : ℤ) (by push_cast; ring) (gridDualMap (meshSequence A i) n) cp2Inverse.f

end HSP.ChainModels
