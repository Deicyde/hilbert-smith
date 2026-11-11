import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Tensor.TensorHomBlocks

/-!
# Blocks of a transported tensor of graded maps

The blocks of `f ⊗ g` followed by the identity transport `r + (d + e) = s` of the target degree.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Kronecker

namespace HSP.ChainModels

open FreeQ DualCat

variable {C C' E E' : ChainComplex FreeQ ℤ}

lemma blockInc_comp_basedTensorHom_comp_eqToHom_comp_blockProj (hE : ∀ q < 0, (E.X q).dim = 0)
    (hE' : ∀ q < 0, (E'.X q).dim = 0) (d e : ℤ) (f : ∀ r, C.X r ⟶ C'.X (r + d))
    (g : ∀ r, E.X r ⟶ E'.X (r + e)) (r s : ℤ) (h : r + (d + e) = s) (p : Fin (r.toNat + 1))
    (q : Fin (s.toNat + 1)) :
    blockInc (tensorSummandDim C E r) p ≫
        (basedTensorHom hE hE' d e f g r ≫ eqToHom (congrArg (basedComplexTensor C' E' hE').X h)) ≫
      blockProj (tensorSummandDim C' E' s) q =
    (if h' : ((q : ℕ) : ℤ) = (p : ℕ) + d then
      (e * (p : ℕ)).negOnePow •
        (basedKron (f (p : ℕ)) (g (r - (p : ℕ))) ≫ eqToHom (by
            simp only [tensorSummandDim]
            rw [h', show s - (((p : ℕ) : ℤ) + d) = r - ((p : ℕ) : ℤ) + e by omega]))
    else 0) := by
  subst h
  refine Eq.trans ?_ (blockInc_comp_basedTensorHom_comp_blockProj hE hE' d e f g r p q)
  simp only [eqToHom_refl]
  erw [Category.comp_id]

end HSP.ChainModels
