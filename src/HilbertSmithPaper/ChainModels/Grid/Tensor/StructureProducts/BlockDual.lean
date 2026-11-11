import Mathlib
import HilbertSmithPaper.ChainModels.Grid.BasedComplexTensor

/-!
# Blocks of a transpose

The block of `X^*` from the summand `q` to the summand `p` is the transpose of the block of `X` from `p` to `q`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Kronecker

namespace HSP.ChainModels

open FreeQ DualCat

private lemma dualHom_blockInc {m : ℕ} (d : Fin m → ℕ) (j : Fin m) :
    dualHom (blockInc d j) = blockProj d j := rfl

private lemma dualHom_blockProj {m : ℕ} (d : Fin m → ℕ) (j : Fin m) :
    dualHom (blockProj d j) = blockInc d j := rfl

lemma blockInc_comp_dualHom_comp_blockProj {m m' : ℕ} (d : Fin m → ℕ) (d' : Fin m' → ℕ)
    (X : (⟨∑ i, d i⟩ : FreeQ) ⟶ ⟨∑ i, d' i⟩) (p : Fin m) (q : Fin m') :
    blockInc d' q ≫ dualHom X ≫ blockProj d p = dualHom (blockInc d p ≫ X ≫ blockProj d' q) := by
  rw [dualHom_comp, dualHom_comp, dualHom_blockInc, dualHom_blockProj, Category.assoc]
  rfl

end HSP.ChainModels
