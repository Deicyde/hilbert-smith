import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.BasedTensor

/-!
# Transpose of a Kronecker product

`(f ⊠ g)^* = f^* ⊠ g^*`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Kronecker

namespace HSP.ChainModels

open FreeQ DualCat

lemma dualHom_basedKron {X X' Y Y' : FreeQ} (f : X ⟶ X') (g : Y ⟶ Y') :
    dualHom (basedKron f g) = basedKron (dualHom f) (dualHom g) := by
  change ((toMatrix f ⊗ₖ toMatrix g).submatrix finProdFinEquiv.symm finProdFinEquiv.symm).transpose
    = ((toMatrix f).transpose ⊗ₖ (toMatrix g).transpose).submatrix finProdFinEquiv.symm
      finProdFinEquiv.symm
  rw [Matrix.transpose_submatrix, Matrix.kroneckerMap_transpose]

end HSP.ChainModels
