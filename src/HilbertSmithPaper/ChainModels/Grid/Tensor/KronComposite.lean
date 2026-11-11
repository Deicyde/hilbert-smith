import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.BasedTensor

/-!
# Kronecker product of composites

`(f ⊠ g)(f' ⊠ g')`-composition: `(f ⊠ g) ≫ (f' ⊠ g') = (f ≫ f') ⊠ (g ≫ g')`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Kronecker

namespace HSP.ChainModels

open FreeQ DualCat

lemma basedKron_comp_basedKron {X X' X'' Y Y' Y'' : FreeQ} (f : X ⟶ X') (f' : X' ⟶ X'')
    (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
    basedKron f g ≫ basedKron f' g' = basedKron (f ≫ f') (g ≫ g') := by
  change (toMatrix f' ⊗ₖ toMatrix g').submatrix finProdFinEquiv.symm finProdFinEquiv.symm *
      (toMatrix f ⊗ₖ toMatrix g).submatrix finProdFinEquiv.symm finProdFinEquiv.symm =
    ((toMatrix f' * toMatrix f) ⊗ₖ (toMatrix g' * toMatrix g)).submatrix
      finProdFinEquiv.symm finProdFinEquiv.symm
  rw [Matrix.submatrix_mul_equiv, Matrix.mul_kronecker_mul]

end HSP.ChainModels
