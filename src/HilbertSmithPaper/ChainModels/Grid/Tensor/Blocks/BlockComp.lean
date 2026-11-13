import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Tensor.Blocks.BlockDecomposition

/-!
# Blocks of a composite

The block `(p, q)` of `G ∘ F` is the sum over the middle blocks of the products of blocks.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Kronecker

namespace HSP.ChainModels

open FreeQ DualCat

lemma block_comp {m m' m'' : ℕ} {d : Fin m → ℕ} {d' : Fin m' → ℕ} {d'' : Fin m'' → ℕ}
    (F : (⟨∑ i, d i⟩ : FreeQ) ⟶ ⟨∑ i, d' i⟩) (G : (⟨∑ i, d' i⟩ : FreeQ) ⟶ ⟨∑ i, d'' i⟩)
    (p : Fin m) (q : Fin m'') :
    blockInc d p ≫ (F ≫ G) ≫ blockProj d'' q =
      ∑ p', (blockInc d p ≫ F ≫ blockProj d' p') ≫ (blockInc d' p' ≫ G ≫ blockProj d'' q) := by
  have : F ≫ G = F ≫ (∑ p', blockProj d' p' ≫ blockInc d' p') ≫ G := by
    rw [blockProj_comp_blockInc_sum, Category.id_comp]
  rw [this]
  simp only [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]

end HSP.ChainModels
