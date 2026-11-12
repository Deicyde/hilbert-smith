import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.BasedStrProd
import HilbertSmithPaper.ChainModels.Grid.Tensor.BlockExtraction

/-!
# Blocks of a product of structures

The block of `(φ ⊗ θ)_{r,s}` from the dual of the summand `a` of degree `s` to the summand `p` of degree `r` is `(-1)^{(r-p)(p+m)} φ_p ⊠ θ_{r-p}` if `a = m - p`, and `0` otherwise.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Kronecker

namespace HSP.ChainModels

open FreeQ DualCat

variable {C E : ChainComplex FreeQ ℤ}

variable (hE : ∀ q < 0, (E.X q).dim = 0)

lemma blockInc_comp_basedStrProd_comp_blockProj (m m' k : ℤ) (hk : m + m' = k)
    (φ : (StructureCx C).X m) (θ : (StructureCx E).X m') (r s : ℤ) (h : r + s = k)
    (a : Fin (s.toNat + 1)) (p : Fin (r.toNat + 1)) :
    blockInc (tensorSummandDim C E s) a ≫
        (basedStrProd C E hE m m' k hk φ θ ⟨(r, s), h⟩ :
          (⟨∑ i, tensorSummandDim C E s i⟩ : FreeQ) ⟶ ⟨∑ i, tensorSummandDim C E r i⟩) ≫
        blockProj (tensorSummandDim C E r) p =
      if h' : ((a : ℕ) : ℤ) = m - (p : ℕ) then
        ((r - (p : ℕ)) * ((p : ℕ) + m)).negOnePow •
          (eqToHom (by
              simp only [dual_eq, tensorSummandDim]
              rw [h', show s - (m - ((p : ℕ) : ℤ)) = m' - (r - ((p : ℕ) : ℤ)) by omega]) ≫
            basedKron (φ ⟨(((p : ℕ) : ℤ), m - (p : ℕ)), by ring⟩)
              (θ ⟨(r - (p : ℕ), m' - (r - (p : ℕ))), by ring⟩))
      else 0 := by
  have e1 : basedStrProd C E hE m m' k hk φ θ ⟨(r, s), h⟩ =
      ∑ a : Fin (s.toNat + 1), ∑ p : Fin (r.toNat + 1),
        blockProj (tensorSummandDim C E s) a ≫
          (if h' : ((a : ℕ) : ℤ) = m - (p : ℕ) then
            ((r - (p : ℕ)) * ((p : ℕ) + m)).negOnePow •
              (eqToHom (by
                  simp only [dual_eq, tensorSummandDim]
                  rw [h', show s - (m - ((p : ℕ) : ℤ)) = m' - (r - ((p : ℕ) : ℤ)) by omega]) ≫
                basedKron (φ ⟨(((p : ℕ) : ℤ), m - (p : ℕ)), by ring⟩)
                  (θ ⟨(r - (p : ℕ), m' - (r - (p : ℕ))), by ring⟩))
          else 0) ≫ blockInc (tensorSummandDim C E r) p := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun a _ => ?_
    by_cases h' : ((a : ℕ) : ℤ) = m - (p : ℕ)
    · simp only [h', ↓reduceDIte]
      rw [Linear.units_smul_comp, Linear.comp_units_smul]
      simp only [Category.assoc]
      rfl
    · simp only [h', ↓reduceDIte]
      rw [zero_comp, comp_zero]
      rfl
  rw [e1]
  exact blockInc_comp_blockSum_comp_blockProj _ _ (fun a p =>
          if h' : ((a : ℕ) : ℤ) = m - (p : ℕ) then
            ((r - (p : ℕ)) * ((p : ℕ) + m)).negOnePow •
              (eqToHom (by
                  simp only [dual_eq, tensorSummandDim]
                  rw [h', show s - (m - ((p : ℕ) : ℤ)) = m' - (r - ((p : ℕ) : ℤ)) by omega]) ≫
                basedKron (φ ⟨(((p : ℕ) : ℤ), m - (p : ℕ)), by ring⟩)
                  (θ ⟨(r - (p : ℕ), m' - (r - (p : ℕ))), by ring⟩))
          else 0) a p

end HSP.ChainModels
