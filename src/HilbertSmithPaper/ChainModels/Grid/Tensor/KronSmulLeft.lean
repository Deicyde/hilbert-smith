import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.BasedTensor

/-!
# Signs in the first factor of a Kronecker product

`(u • f) ⊠ g = u • (f ⊠ g)` for `u : ℤˣ`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Kronecker

namespace HSP.ChainModels

open FreeQ DualCat

lemma basedKron_units_smul_left {X₀ X₁ Y₀ Y₁ : FreeQ} (u : ℤˣ) (f : X₀ ⟶ X₁)
    (g : Y₀ ⟶ Y₁) : basedKron (u • f) g = u • basedKron f g := by
  rw [Units.smul_def, Units.smul_def]
  change (((u : ℤ) • toMatrix f) ⊗ₖ toMatrix g).submatrix _ _ =
    (u : ℤ) • (toMatrix f ⊗ₖ toMatrix g).submatrix _ _
  rw [Matrix.smul_kronecker]; rfl

end HSP.ChainModels
