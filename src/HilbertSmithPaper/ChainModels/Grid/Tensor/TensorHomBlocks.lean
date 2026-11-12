import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Tensor.BasedTensorHom
import HilbertSmithPaper.ChainModels.Grid.Tensor.Blocks.BlockExtraction

/-!
# Blocks of a tensor of graded maps

The block of `f ⊗ g` from the summand `C_p ⊠ E_{r-p}` to the summand `q` is `(-1)^{e p} f_p ⊠ g_{r-p}` (with the transport of the summand) if `q = p + d`, and `0` otherwise.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Kronecker

namespace HSP.ChainModels

open FreeQ DualCat

variable {C C' E E' : ChainComplex FreeQ ℤ}

lemma blockInc_comp_basedTensorHom_comp_blockProj (hE : ∀ q < 0, (E.X q).dim = 0) (hE' : ∀ q < 0, (E'.X q).dim = 0)
    (d e : ℤ) (f : ∀ r, C.X r ⟶ C'.X (r + d)) (g : ∀ r, E.X r ⟶ E'.X (r + e)) (r : ℤ)
    (p : Fin (r.toNat + 1)) (q : Fin ((r + (d + e)).toNat + 1)) :
    blockInc (tensorSummandDim C E r) p ≫ basedTensorHom hE hE' d e f g r ≫
      blockProj (tensorSummandDim C' E' (r + (d + e))) q =
    if h : ((q : ℕ) : ℤ) = (p : ℕ) + d then
      (e * (p : ℕ)).negOnePow •
        (basedKron (f (p : ℕ)) (g (r - (p : ℕ))) ≫ eqToHom (by
            simp only [tensorSummandDim]
            rw [h, show r + (d + e) - (((p : ℕ) : ℤ) + d) = r - ((p : ℕ) : ℤ) + e by ring]))
    else 0 := by
  have e1 : basedTensorHom hE hE' d e f g r = ∑ a : Fin (r.toNat + 1),
      ∑ a' : Fin ((r + (d + e)).toNat + 1), blockProj (tensorSummandDim C E r) a ≫
      (if h : ((a' : ℕ) : ℤ) = (a : ℕ) + d then (e * (a : ℕ)).negOnePow •
        (basedKron (f (a : ℕ)) (g (r - (a : ℕ))) ≫ eqToHom (by
            simp only [tensorSummandDim]
            rw [h, show r + (d + e) - (((a : ℕ) : ℤ) + d) = r - ((a : ℕ) : ℤ) + e by ring]))
       else 0) ≫ blockInc (tensorSummandDim C' E' (r + (d + e))) a' := by
    unfold basedTensorHom
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
    by_cases h : ((a' : ℕ) : ℤ) = (a : ℕ) + d
    · simp only [h, ↓reduceDIte]
      rw [Linear.units_smul_comp, Linear.comp_units_smul]
      simp only [Category.assoc]
      rfl
    · simp only [h, ↓reduceDIte]
      rw [zero_comp, comp_zero]
      rfl
  rw [e1]
  exact blockInc_comp_blockSum_comp_blockProj _ _ (fun (a : Fin (r.toNat + 1))
    (a' : Fin ((r + (d + e)).toNat + 1)) =>
      if h : ((a' : ℕ) : ℤ) = (a : ℕ) + d then (e * (a : ℕ)).negOnePow •
        (basedKron (f (a : ℕ)) (g (r - (a : ℕ))) ≫ eqToHom (by
            simp only [tensorSummandDim]
            rw [h, show r + (d + e) - (((a : ℕ) : ℤ) + d) = r - ((a : ℕ) : ℤ) + e by ring]))
       else 0) p q

end HSP.ChainModels
