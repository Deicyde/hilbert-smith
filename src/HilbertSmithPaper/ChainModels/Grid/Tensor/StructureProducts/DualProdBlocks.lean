import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.BasedDualProd
import HilbertSmithPaper.ChainModels.Grid.Tensor.BlockExtraction

/-!
# Blocks of a product of duality maps

The block of `Ξ^{-1}(f ⊗ g)` from the summand `a` of degree `r` to the dual of the summand `q` of degree `k - r` is `(-1)^{(r-a)(a+m)} f_a ⊠ g_{r-a}` if `q = m - a`, and `0` otherwise.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Kronecker

namespace HSP.ChainModels

open FreeQ DualCat

variable {C E : ChainComplex FreeQ ℤ}

variable (hE : ∀ q < 0, (E.X q).dim = 0)

lemma blockInc_comp_basedDualProd_comp_blockProj (m m' k : ℤ) (hk : m + m' = k)
    (f : ∀ r, C.X r ⟶ dual (C.X (m - r))) (g : ∀ r, E.X r ⟶ dual (E.X (m' - r))) (r : ℤ)
    (a : Fin (r.toNat + 1)) (q : Fin ((k - r).toNat + 1)) :
    blockInc (tensorSummandDim C E r) a ≫
        (basedDualProd C E hE m m' k hk f g r :
          (⟨∑ i, tensorSummandDim C E r i⟩ : FreeQ) ⟶ ⟨∑ i, tensorSummandDim C E (k - r) i⟩) ≫
        blockProj (tensorSummandDim C E (k - r)) q =
      if h : ((q : ℕ) : ℤ) = m - (a : ℕ) then
        ((r - (a : ℕ)) * ((a : ℕ) + m)).negOnePow •
          (basedKron (f (a : ℕ)) (g (r - (a : ℕ))) ≫ eqToHom (by
            simp only [dual_eq, tensorSummandDim]
            rw [h, show k - r - (m - ((a : ℕ) : ℤ)) = m' - (r - ((a : ℕ) : ℤ)) by omega]))
      else 0 := by
  have e1 : basedDualProd C E hE m m' k hk f g r =
      ∑ a : Fin (r.toNat + 1), ∑ q : Fin ((k - r).toNat + 1),
        blockProj (tensorSummandDim C E r) a ≫
          (if h : ((q : ℕ) : ℤ) = m - (a : ℕ) then
            ((r - (a : ℕ)) * ((a : ℕ) + m)).negOnePow •
              (basedKron (f (a : ℕ)) (g (r - (a : ℕ))) ≫ eqToHom (by
                simp only [dual_eq, tensorSummandDim]
                rw [h, show k - r - (m - ((a : ℕ) : ℤ)) = m' - (r - ((a : ℕ) : ℤ)) by omega]))
          else 0) ≫ blockInc (tensorSummandDim C E (k - r)) q := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun q _ => ?_
    by_cases h : ((q : ℕ) : ℤ) = m - (a : ℕ)
    · simp only [h, ↓reduceDIte]
      rw [Linear.units_smul_comp, Linear.comp_units_smul]
      simp only [Category.assoc]
      rfl
    · simp only [h, ↓reduceDIte]
      rw [zero_comp, comp_zero]
      rfl
  rw [e1]
  exact blockInc_comp_blockSum_comp_blockProj _ _ (fun a q =>
    if h : ((q : ℕ) : ℤ) = m - (a : ℕ) then
      ((r - (a : ℕ)) * ((a : ℕ) + m)).negOnePow •
        (basedKron (f (a : ℕ)) (g (r - (a : ℕ))) ≫ eqToHom (by
          simp only [dual_eq, tensorSummandDim]
          rw [h, show k - r - (m - ((a : ℕ) : ℤ)) = m' - (r - ((a : ℕ) : ℤ)) by omega]))
    else 0) a q

end HSP.ChainModels
