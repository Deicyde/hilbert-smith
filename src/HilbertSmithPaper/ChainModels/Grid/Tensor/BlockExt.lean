import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Tensor.BlockDecomposition

/-!
# Maps between concatenations are determined by their blocks

Two maps `ℚ^{∑ d} → ℚ^{∑ d'}` with the same blocks are equal.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Kronecker

namespace HSP.ChainModels

open FreeQ DualCat

lemma block_ext {m m' : ℕ} {d : Fin m → ℕ} {d' : Fin m' → ℕ}
    {F G : (⟨∑ i, d i⟩ : FreeQ) ⟶ ⟨∑ i, d' i⟩}
    (h : ∀ p q, blockInc d p ≫ F ≫ blockProj d' q = blockInc d p ≫ G ≫ blockProj d' q) :
    F = G := by
  have e : ∀ H : (⟨∑ i, d i⟩ : FreeQ) ⟶ ⟨∑ i, d' i⟩,
      H = ∑ p, ∑ q, blockProj d p ≫ (blockInc d p ≫ H ≫ blockProj d' q) ≫ blockInc d' q := by
    intro H
    conv_lhs => rw [← Category.id_comp H, ← Category.comp_id H, ← blockProj_comp_blockInc_sum d,
      ← blockProj_comp_blockInc_sum d']
    simp only [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
    exact Finset.sum_comm
  rw [e F, e G]
  simp only [h]

end HSP.ChainModels
