import Mathlib
import HilbertSmithPaper.ChainModels.Grid.BasedComplexTensor

/-!
# Transport of summand projections

For `s = t`, the identity transport `(C ⊗ E)_s = (C ⊗ E)_t` followed by the projection onto a summand of degree `t` is the projection onto the same summand of degree `s` followed by the transport of the summand.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Kronecker

namespace HSP.ChainModels

open FreeQ DualCat

variable {C E : ChainComplex FreeQ ℤ}

lemma eqToHom_comp_blockProj (hE : ∀ q < 0, (E.X q).dim = 0) {s t : ℤ} (h : s = t)
    (q : Fin (t.toNat + 1)) :
    eqToHom (congrArg (basedComplexTensor C E hE).X h) ≫ blockProj (tensorSummandDim C E t) q =
      blockProj (tensorSummandDim C E s) (Fin.cast (by rw [h]) q) ≫
        eqToHom (by subst h; rfl) := by
  subst h
  simp only [eqToHom_refl, Category.comp_id]
  exact Category.id_comp _

end HSP.ChainModels
