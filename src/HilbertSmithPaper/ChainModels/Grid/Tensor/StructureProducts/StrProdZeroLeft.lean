import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.BasedStrProd
import HilbertSmithPaper.ChainModels.Grid.Tensor.KronZero

/-!
# A product of structures with a zero left factor

`0 ⊗ θ = 0`: every block is a Kronecker product with a zero factor.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.ChainModels

open FreeQ DualCat

/-- *A product of structures with a zero left factor vanishes*: `0 ⊗ θ = 0`. -/
lemma basedStrProd_zero_left {C E : ChainComplex FreeQ ℤ} (hE : ∀ q < 0, (E.X q).dim = 0)
    (m m' k : ℤ) (hk : m + m' = k) (θ : (StructureCx E).X m') :
    basedStrProd C E hE m m' k hk 0 θ = 0 := by
  funext x
  refine (Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_).trans rfl
  by_cases h' : ((b : ℕ) : ℤ) = m - (a : ℕ)
  · simp only [h', ↓reduceDIte]
    rw [show ((0 : (StructureCx C).X m) ⟨(((a : ℕ) : ℤ), m - (a : ℕ)), by ring⟩) = 0 from rfl,
      basedKron_eq_zero (Or.inl rfl)]
    simp only [zero_comp, comp_zero, smul_zero]
    rfl
  · simp only [h', ↓reduceDIte]

end HSP.ChainModels
