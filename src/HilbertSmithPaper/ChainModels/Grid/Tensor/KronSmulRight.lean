import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.BasedTensor

/-!
# Signs in the second factor of a Kronecker product

`f ⊠ (u • g) = u • (f ⊠ g)` for `u : ℤˣ`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Kronecker

namespace HSP.ChainModels

open FreeQ DualCat

lemma basedKron_units_smul_right {X₀ X₁ Y₀ Y₁ : FreeQ} (u : ℤˣ) (f : X₀ ⟶ X₁)
    (g : Y₀ ⟶ Y₁) : basedKron f (u • g) = u • basedKron f g := by
  rw [Units.smul_def, Units.smul_def]
  change (toMatrix f ⊗ₖ ((u : ℤ) • toMatrix g)).submatrix _ _ =
    (u : ℤ) • (toMatrix f ⊗ₖ toMatrix g).submatrix _ _
  rw [Matrix.kronecker_smul]; rfl

end HSP.ChainModels
