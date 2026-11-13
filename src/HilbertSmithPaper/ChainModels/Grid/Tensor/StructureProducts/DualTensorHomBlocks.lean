import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Tensor.BasedDualTensorHom
import HilbertSmithPaper.ChainModels.Grid.Tensor.Blocks.BlockExtraction

/-!
# Blocks of a dual tensor of graded maps

The blocks of `Ξ^{-1}(F ⊗ G)Ξ`, followed by the identity transport `r + (d + e) = s` of the target degree.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Kronecker

namespace HSP.ChainModels

open FreeQ DualCat

variable {C E : ChainComplex FreeQ ℤ}

variable (hE : ∀ q < 0, (E.X q).dim = 0)

lemma blockInc_comp_basedDualTensorHom_comp_eqToHom_comp_blockProj (m m' k : ℤ) (hk : m + m' = k)
    (d e : ℤ) (F : ∀ r, dual (C.X (m - r)) ⟶ dual (C.X (m - (r + d))))
    (G : ∀ r, dual (E.X (m' - r)) ⟶ dual (E.X (m' - (r + e)))) (r s : ℤ) (h : r + (d + e) = s)
    (p : Fin ((k - r).toNat + 1)) (q : Fin ((k - s).toNat + 1)) :
    blockInc (tensorSummandDim C E (k - r)) p ≫
        ((basedDualTensorHom hE m m' k hk d e F G r ≫
            eqToHom (congrArg (fun u => dual ((basedComplexTensor C E hE).X (k - u))) h)) :
          (⟨∑ i, tensorSummandDim C E (k - r) i⟩ : FreeQ) ⟶ ⟨∑ i, tensorSummandDim C E (k - s) i⟩) ≫
        blockProj (tensorSummandDim C E (k - s)) q =
      if h' : ((q : ℕ) : ℤ) = (p : ℕ) - d then
        (((r - (m - (p : ℕ))) + e) * ((m - (p : ℕ)) + d + m) + e * (m - (p : ℕ)) +
            (r - (m - (p : ℕ))) * ((m - (p : ℕ)) + m)).negOnePow •
          (eqToHom (by
              simp only [tensorSummandDim, dual_eq]
              rw [show m - (m - ((p : ℕ) : ℤ)) = ((p : ℕ) : ℤ) by ring,
                show m' - (r - (m - ((p : ℕ) : ℤ))) = k - r - ((p : ℕ) : ℤ) by omega]) ≫
            basedKron (F (m - (p : ℕ))) (G (r - (m - (p : ℕ)))) ≫
            eqToHom (by
              simp only [tensorSummandDim, dual_eq]
              rw [h', show m - (m - ((p : ℕ) : ℤ) + d) = ((p : ℕ) : ℤ) - d by ring,
                show m' - (r - (m - ((p : ℕ) : ℤ)) + e) = k - s - (((p : ℕ) : ℤ) - d) by omega]))
      else 0 := by
  subst h
  have e1 : basedDualTensorHom hE m m' k hk d e F G r =
      ∑ p : Fin ((k - r).toNat + 1), ∑ q : Fin ((k - (r + (d + e))).toNat + 1),
        blockProj (tensorSummandDim C E (k - r)) p ≫
          (if h' : ((q : ℕ) : ℤ) = (p : ℕ) - d then
            (((r - (m - (p : ℕ))) + e) * ((m - (p : ℕ)) + d + m) + e * (m - (p : ℕ)) +
                (r - (m - (p : ℕ))) * ((m - (p : ℕ)) + m)).negOnePow •
              (eqToHom (by
                  simp only [tensorSummandDim, dual_eq]
                  rw [show m - (m - ((p : ℕ) : ℤ)) = ((p : ℕ) : ℤ) by ring,
                    show m' - (r - (m - ((p : ℕ) : ℤ))) = k - r - ((p : ℕ) : ℤ) by omega]) ≫
                basedKron (F (m - (p : ℕ))) (G (r - (m - (p : ℕ)))) ≫
                eqToHom (by
                  simp only [tensorSummandDim, dual_eq]
                  rw [h', show m - (m - ((p : ℕ) : ℤ) + d) = ((p : ℕ) : ℤ) - d by ring,
                    show m' - (r - (m - ((p : ℕ) : ℤ)) + e) =
                      k - (r + (d + e)) - (((p : ℕ) : ℤ) - d) by omega]))
          else 0) ≫ blockInc (tensorSummandDim C E (k - (r + (d + e)))) q := by
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    by_cases h' : ((q : ℕ) : ℤ) = (p : ℕ) - d
    · simp only [h', ↓reduceDIte]
      rw [Linear.units_smul_comp, Linear.comp_units_smul]
      simp only [Category.assoc]
      rfl
    · simp only [h', ↓reduceDIte]
      rw [zero_comp, comp_zero]
      rfl
  erw [eqToHom_refl, Category.comp_id]
  rw [e1]
  exact blockInc_comp_blockSum_comp_blockProj _ _ (fun p q =>
    if h' : ((q : ℕ) : ℤ) = (p : ℕ) - d then
      (((r - (m - (p : ℕ))) + e) * ((m - (p : ℕ)) + d + m) + e * (m - (p : ℕ)) +
          (r - (m - (p : ℕ))) * ((m - (p : ℕ)) + m)).negOnePow •
        (eqToHom (by
            simp only [tensorSummandDim, dual_eq]
            rw [show m - (m - ((p : ℕ) : ℤ)) = ((p : ℕ) : ℤ) by ring,
              show m' - (r - (m - ((p : ℕ) : ℤ))) = k - r - ((p : ℕ) : ℤ) by omega]) ≫
          basedKron (F (m - (p : ℕ))) (G (r - (m - (p : ℕ)))) ≫
          eqToHom (by
            simp only [tensorSummandDim, dual_eq]
            rw [h', show m - (m - ((p : ℕ) : ℤ) + d) = ((p : ℕ) : ℤ) - d by ring,
              show m' - (r - (m - ((p : ℕ) : ℤ)) + e) = k - (r + (d + e)) - (((p : ℕ) : ℤ) - d) by
                omega]))
    else 0) p q

end HSP.ChainModels
