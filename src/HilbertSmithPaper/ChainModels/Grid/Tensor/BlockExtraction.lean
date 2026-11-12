import Mathlib
import HilbertSmithPaper.ChainModels.Grid.BasedComplexTensor
import HilbertSmithPaper.ChainModels.Grid.Tensor.BlockProjections

/-!
# Block extraction

The block `(p, q)` of a map assembled from blocks `X a a'` is `X p q`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Kronecker

namespace HSP.ChainModels

open FreeQ DualCat

lemma blockInc_comp_blockSum_comp_blockProj {m m' : ℕ} (d : Fin m → ℕ) (d' : Fin m' → ℕ)
    (X : ∀ a a', (⟨d a⟩ : FreeQ) ⟶ ⟨d' a'⟩) (p : Fin m) (q : Fin m') :
    blockInc d p ≫ (∑ a, ∑ a', blockProj d a ≫ X a a' ≫ blockInc d' a') ≫ blockProj d' q =
      X p q := by
  simp only [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
  rw [Finset.sum_eq_single p]
  · rw [Finset.sum_eq_single q]
    · rw [blockInc_proj_self_assoc, blockInc_proj_self, Category.comp_id]
    · intro b _ hb
      rw [blockInc_proj_self_assoc, blockInc_proj_ne _ hb, comp_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro b _ hb
    simp only [blockInc_proj_ne_assoc _ (Ne.symm hb), zero_comp, Finset.sum_const_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

end HSP.ChainModels
