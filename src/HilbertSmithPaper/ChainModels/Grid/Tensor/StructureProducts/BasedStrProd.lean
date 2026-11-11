import Mathlib
import HilbertSmithPaper.ChainModels.Grid.BasedComplexTensor
import HilbertSmithPaper.LTheory.Base.Complexes.StructureComplex

/-!
# Product of structures in explicit bases

For `φ ∈ M(C)_m`, `θ ∈ M(E)_{m'}` and `k = m + m'`, the external product `φ ⊗ θ ∈ M(C ⊗ E)_k`, computed in the explicit bases of the tensor product of based complexes: its block from the dual of the summand `C_{m-p} ⊠ E_{m'-q}` (identified with `C_{m-p}^* ⊠ E_{m'-q}^*`, with no sign) to the summand `C_p ⊠ E_q` is `(-1)^{q(p+m)} φ_p ⊠ θ_q`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Kronecker

namespace HSP.ChainModels

open FreeQ DualCat

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

end HSP.ChainModels
