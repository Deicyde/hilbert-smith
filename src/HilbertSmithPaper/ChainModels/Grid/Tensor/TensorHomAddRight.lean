import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Tensor.BasedTensorHom
import HilbertSmithPaper.ChainModels.Grid.Tensor.KronAddRight

/-!
# Additivity of tensors of graded maps in the second factor

`f ⊗ (g + g') = f ⊗ g + f ⊗ g'`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Kronecker

namespace HSP.ChainModels

open FreeQ DualCat

variable {C C' E E' : ChainComplex FreeQ ℤ}

theorem basedTensorHom_add_right (hE : ∀ q < 0, (E.X q).dim = 0) (hE' : ∀ q < 0, (E'.X q).dim = 0)
    (d e : ℤ) (f : ∀ r, C.X r ⟶ C'.X (r + d)) (g g' : ∀ r, E.X r ⟶ E'.X (r + e)) (r : ℤ) :
    basedTensorHom hE hE' d e f (g + g') r =
      basedTensorHom hE hE' d e f g r + basedTensorHom hE hE' d e f g' r := by
  simp only [basedTensorHom, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
  by_cases h : ((a' : ℕ) : ℤ) = (a : ℕ) + d
  · simp only [h, ↓reduceDIte, Pi.add_apply, basedKron_add_right, Preadditive.add_comp,
      Preadditive.comp_add, smul_add]
    rfl
  · simp only [h, ↓reduceDIte, add_zero]

end HSP.ChainModels
