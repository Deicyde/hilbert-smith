import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.BasedTensor

/-!
# Kronecker product of identity transports

The Kronecker product of two identity transports is an identity transport.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Kronecker

namespace HSP.ChainModels

open FreeQ DualCat

lemma basedKron_eqToHom {X X' Y Y' : FreeQ} (hX : X = X') (hY : Y = Y') :
    basedKron (eqToHom hX) (eqToHom hY) = eqToHom (by rw [hX, hY]) := by
  subst hX hY
  change ((1 : Matrix (Fin X.dim) (Fin X.dim) ℚ) ⊗ₖ (1 : Matrix (Fin Y.dim) (Fin Y.dim) ℚ)).submatrix
    finProdFinEquiv.symm finProdFinEquiv.symm = 1
  rw [Matrix.one_kronecker_one, Matrix.submatrix_one_equiv]

end HSP.ChainModels
