import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.BasedTensor

/-!
# Additivity of the Kronecker product in the second factor

`f ⊠ (g + g') = f ⊠ g + f ⊠ g'`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Kronecker

namespace HSP.ChainModels

open FreeQ DualCat

lemma basedKron_add_right {X₀ X₁ Y₀ Y₁ : FreeQ} (f : X₀ ⟶ X₁) (g g' : Y₀ ⟶ Y₁) :
    basedKron f (g + g') = basedKron f g + basedKron f g' := by
  change (toMatrix f ⊗ₖ (toMatrix g + toMatrix g')).submatrix _ _ =
    (toMatrix f ⊗ₖ toMatrix g).submatrix _ _ + (toMatrix f ⊗ₖ toMatrix g').submatrix _ _
  rw [Matrix.kronecker_add]; rfl

end HSP.ChainModels
