import Mathlib
import HilbertSmithPaper.ChainModels.Grid.BasedComplexTensor

/-!
# Block decomposition of the identity

The identity of a concatenation `ℚ^{∑ d}` is the sum over the blocks of the projection onto a block followed by its inclusion.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Kronecker

namespace HSP.ChainModels

open FreeQ DualCat

lemma blockProj_comp_blockInc_sum {m : ℕ} (d : Fin m → ℕ) :
    ∑ j, blockProj d j ≫ blockInc d j = 𝟙 _ := by
  refine Matrix.ext fun x y => ?_
  have key : ∀ x y : Fin (∑ i, d i), ∑ j, ∑ b : Fin (d j),
      (if finSigmaFinEquiv.symm x = ⟨j, b⟩ then (1 : ℚ) else 0) *
        (if finSigmaFinEquiv.symm y = ⟨j, b⟩ then 1 else 0) = if x = y then 1 else 0 := by
    intro x y
    rw [← Fintype.sum_sigma (fun s : (Σ j, Fin (d j)) =>
      (if finSigmaFinEquiv.symm x = s then (1 : ℚ) else 0) *
        (if finSigmaFinEquiv.symm y = s then 1 else 0))]
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ↓reduceIte]
    by_cases h : x = y
    · subst h; simp
    · have h' : finSigmaFinEquiv.symm x ≠ finSigmaFinEquiv.symm y :=
        fun h' => h (finSigmaFinEquiv.symm.injective h')
      simp [h, h'.symm]
  change (∑ j, toMatrix (blockProj d j ≫ blockInc d j)) x y = (1 : Matrix (Fin (∑ i, d i)) _ ℚ) x y
  rw [Matrix.one_apply, Matrix.sum_apply, ← key]
  rfl

end HSP.ChainModels
