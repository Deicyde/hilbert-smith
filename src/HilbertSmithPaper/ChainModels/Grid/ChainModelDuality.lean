import Mathlib
import HilbertSmithPaper.ChainModels.Grid.ChainModel
import HilbertSmithPaper.ChainModels.Grid.CircleDuality
import HilbertSmithPaper.ChainModels.Grid.Cp2Cells
import HilbertSmithPaper.LTheory.Base.Complexes.DualComplex
import HilbertSmithPaper.LTheory.Base.Complexes.StructureComplex
import HilbertSmithPaper.ChainModels.Grid.Cp2DimNeg

/-!
# Chain-model duality

The duality data of `D_i`: the structure `φ_i ∈ M(D_i)_N`, the iterated external product
`(⋯(φ^s ⊗ φ^s) ⊗ ⋯ ⊗ φ^s) ⊗ φ_P`, and the map `b_i = Ξ^{-1} ∘ (b ⊗ ⋯ ⊗ b ⊗ b_P) : D_i → D_i^{N-*}`,
`N = n + 4`.

## Encoding

* All products are computed in the explicit bases of the tensor product of based complexes. For
  `φ ∈ M(C)_m`, `θ ∈ M(E)_{m'}` and `k = m + m'`, `basedStrProd` is the external product of
  structures: its block from the dual of the summand `C_{m-p} ⊠ E_{m'-q}` of `(C ⊗ E)_{k-r}`
  (identified with `C_{m-p}^* ⊠ E_{m'-q}^*` with no sign; the duality of based vector spaces is the
  transpose) to the summand `C_p ⊠ E_q` of `(C ⊗ E)_r` is `(-1)^{q(p+m)} φ_p ⊠ θ_q`.
* For degree-`0` maps `f_r : C_r → C^*_{m-r}` and `g_r : E_r → E^*_{m'-r}`, `basedDualProd` is
  `Ξ^{-1} ∘ (f ⊗ g)`: the block from `C_a ⊠ E_c` to the dual of `C_{m-a} ⊠ E_{m'-c}` is
  `(-1)^{c(a+m)} f_a ⊠ g_c`, the sign of the dual of a tensor product.
* The iterates start from the unit complex `𝟙` (structure and map the identity of `ℚ` in degree
  `0`), as `C(k)` does; the first step multiplies by the unit with sign `+1`.
* `chainModelDuality A i` (the declaration of the article) is the pair `(φ_i, b_i)`, with `b_i`
  given by its components `(b_i)_r : (D_i)_r → (D_i^{N-*})_r`.
-/

open CategoryTheory

namespace HSP.ChainModels

open FreeQ DualCat

section Products

variable (C E : ChainComplex FreeQ ℤ) (hE : ∀ q < 0, (E.X q).dim = 0)

/-- The external product `φ ⊗ θ ∈ M(C ⊗ E)_k` of `φ ∈ M(C)_m` and `θ ∈ M(E)_{m'}`, `m + m' = k`:
the block from the dual of `C_{m-p} ⊠ E_{m'-q}` to `C_p ⊠ E_q` is `(-1)^{q(p+m)} φ_p ⊠ θ_q`. -/
noncomputable def basedStrProd (m m' k : ℤ) (hk : m + m' = k) (φ : (StructureCx C).X m)
    (θ : (StructureCx E).X m') : (StructureCx (basedComplexTensor C E hE)).X k :=
  fun x =>
    ∑ p : Fin (x.1.1.toNat + 1), ∑ p' : Fin (x.1.2.toNat + 1),
      if h : ((p' : ℕ) : ℤ) = m - (p : ℕ) then
        ((x.1.1 - (p : ℕ)) * ((p : ℕ) + m)).negOnePow •
          (blockProj (tensorSummandDim C E x.1.2) p' ≫
            eqToHom (by
              have hx := x.2
              simp only [dual_eq, tensorSummandDim]
              rw [h, show x.1.2 - (m - ((p : ℕ) : ℤ)) = m' - (x.1.1 - ((p : ℕ) : ℤ)) by omega]) ≫
            basedKron (φ ⟨(((p : ℕ) : ℤ), m - (p : ℕ)), by ring⟩)
              (θ ⟨(x.1.1 - (p : ℕ), m' - (x.1.1 - (p : ℕ))), by ring⟩) ≫
            blockInc (tensorSummandDim C E x.1.1) p)
      else 0

/-- The degree-`0` map `Ξ^{-1} ∘ (f ⊗ g) : C ⊗ E → (C ⊗ E)^{k-*}` of `f_r : C_r → C^*_{m-r}` and
`g_r : E_r → E^*_{m'-r}`, `m + m' = k`: the block from `C_a ⊠ E_c` to the dual of
`C_{m-a} ⊠ E_{m'-c}` is `(-1)^{c(a+m)} f_a ⊠ g_c`. -/
noncomputable def basedDualProd (m m' k : ℤ) (hk : m + m' = k)
    (f : ∀ r, C.X r ⟶ dual (C.X (m - r))) (g : ∀ r, E.X r ⟶ dual (E.X (m' - r))) (r : ℤ) :
    (basedComplexTensor C E hE).X r ⟶ dual ((basedComplexTensor C E hE).X (k - r)) :=
  ∑ a : Fin (r.toNat + 1), ∑ a' : Fin ((k - r).toNat + 1),
    if h : ((a' : ℕ) : ℤ) = m - (a : ℕ) then
      ((r - (a : ℕ)) * ((a : ℕ) + m)).negOnePow •
        (blockProj (tensorSummandDim C E r) a ≫
          basedKron (f (a : ℕ)) (g (r - (a : ℕ))) ≫
          eqToHom (by
            simp only [dual_eq, tensorSummandDim]
            rw [h, show k - r - (m - ((a : ℕ) : ℤ)) = m' - (r - ((a : ℕ) : ℤ)) by omega]) ≫
          blockInc (tensorSummandDim C E (k - r)) a')
    else 0

end Products

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

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- *Chain-model duality*: `φ_i = (⋯(φ^s ⊗ φ^s) ⊗ ⋯ ⊗ φ^s) ⊗ φ_P ∈ M(D_i)_N` and
`b_i = Ξ^{-1} ∘ (b ⊗ ⋯ ⊗ b ⊗ b_P)`, `N = n + 4`. -/
noncomputable def chainModelDuality (A : LocalDatum p n D ρplus) (i : ℕ) :
    ChainModelDualityData (chainModel A i) ((n + 4 : ℕ) : ℤ) where
  φ := basedStrProd (gridComplex (meshSequence A i) n) cp2Complex cp2Complex_dim_neg n 4
    ((n + 4 : ℕ) : ℤ) (by push_cast; ring) (gridStructure (meshSequence A i) n) cp2Structure
  b := basedDualProd (gridComplex (meshSequence A i) n) cp2Complex cp2Complex_dim_neg n 4
    ((n + 4 : ℕ) : ℤ) (by push_cast; ring) (gridDualMap (meshSequence A i) n) cp2Inverse.f

end HSP.ChainModels
