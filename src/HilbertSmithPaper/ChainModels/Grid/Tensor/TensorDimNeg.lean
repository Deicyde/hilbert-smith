import Mathlib
import HilbertSmithPaper.ChainModels.Grid.BasedComplexTensor

/-!
# The tensor product vanishes in negative degrees

If `E` vanishes in negative degrees, so does `C ⊗ E`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Kronecker

namespace HSP.ChainModels

open FreeQ DualCat

variable {C E : ChainComplex FreeQ ℤ}

lemma basedComplexTensor_dim_neg (hE : ∀ q < 0, (E.X q).dim = 0) :
    ∀ q < 0, ((basedComplexTensor C E hE).X q).dim = 0 := by
  intro q hq
  change ∑ p : Fin (q.toNat + 1), (C.X (p : ℕ)).dim * (E.X (q - (p : ℕ))).dim = 0
  refine Finset.sum_eq_zero fun p _ => ?_
  have : (p : ℕ) = 0 := by have := p.2; omega
  rw [hE _ (by omega), mul_zero]

end HSP.ChainModels
