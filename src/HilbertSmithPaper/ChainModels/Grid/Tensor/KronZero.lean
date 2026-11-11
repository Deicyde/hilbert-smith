import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.BasedTensor

/-!
# Kronecker product with a zero factor

`f ⊠ g = 0` when `f = 0` or `g = 0`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Kronecker

namespace HSP.ChainModels

open FreeQ DualCat

lemma basedKron_eq_zero {X₀ X₁ Y₀ Y₁ : FreeQ} {f : X₀ ⟶ X₁} {g : Y₀ ⟶ Y₁} (h : f = 0 ∨ g = 0) :
    basedKron f g = 0 := by
  rcases h with rfl | rfl
  · change ((0 : Matrix (Fin X₁.dim) (Fin X₀.dim) ℚ) ⊗ₖ toMatrix g).submatrix _ _ = 0
    rw [Matrix.zero_kronecker, Matrix.submatrix_zero]; rfl
  · change (toMatrix f ⊗ₖ (0 : Matrix (Fin Y₁.dim) (Fin Y₀.dim) ℚ)).submatrix _ _ = 0
    rw [Matrix.kronecker_zero, Matrix.submatrix_zero]; rfl

end HSP.ChainModels
