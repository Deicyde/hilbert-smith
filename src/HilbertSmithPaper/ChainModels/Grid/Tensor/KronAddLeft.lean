import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.BasedTensor

/-!
# Additivity of the Kronecker product in the first factor

`(f + f') ⊠ g = f ⊠ g + f' ⊠ g`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Kronecker

namespace HSP.ChainModels

open FreeQ DualCat

lemma basedKron_add_left {X₀ X₁ Y₀ Y₁ : FreeQ} (f f' : X₀ ⟶ X₁) (g : Y₀ ⟶ Y₁) :
    basedKron (f + f') g = basedKron f g + basedKron f' g := by
  change ((toMatrix f + toMatrix f') ⊗ₖ toMatrix g).submatrix _ _ =
    (toMatrix f ⊗ₖ toMatrix g).submatrix _ _ + (toMatrix f' ⊗ₖ toMatrix g).submatrix _ _
  rw [Matrix.add_kronecker]; rfl

end HSP.ChainModels
