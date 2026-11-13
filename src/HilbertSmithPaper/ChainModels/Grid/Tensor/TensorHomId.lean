import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Tensor.BasedTensorHom
import HilbertSmithPaper.ChainModels.Grid.Tensor.IdDeg0
import HilbertSmithPaper.ChainModels.Grid.Tensor.Blocks.BlockDecomposition
import HilbertSmithPaper.ChainModels.Grid.Tensor.KronTransport

/-!
# Tensor of identities

The tensor of the identities of `C` and `E`, as maps of degree `0`, is the identity of `C ⊗ E` (up to the identity transport `r = r + (0 + 0)`).
-/

open CategoryTheory CategoryTheory.Limits
open scoped Kronecker

namespace HSP.ChainModels

open FreeQ DualCat

variable {C E : ChainComplex FreeQ ℤ}

private lemma sum_transport (hE : ∀ q < 0, (E.X q).dim = 0) {s t : ℤ} (h : s = t) :
    ∑ a : Fin (s.toNat + 1), blockProj (tensorSummandDim C E s) a ≫
      eqToHom (by subst h; rfl) ≫ blockInc (tensorSummandDim C E t) (Fin.cast (by rw [h]) a) =
    eqToHom (congrArg (basedComplexTensor C E hE).X h) := by
  subst h
  simp only [eqToHom_refl, Category.id_comp, Fin.cast_eq_self]
  exact blockProj_comp_blockInc_sum _

theorem basedTensorHom_id (hE : ∀ q < 0, (E.X q).dim = 0) (r : ℤ) :
    basedTensorHom hE hE 0 0 (idDeg0 C) (idDeg0 E) r =
      eqToHom (congrArg (basedComplexTensor C E hE).X (by ring)) := by
  rw [← sum_transport hE (show r = r + (0 + 0) by ring)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single (Fin.cast (by rw [show r + (0 + 0) = r by ring]) a)]
  · have h : (((Fin.cast (by rw [show r + (0 + 0) = r by ring]) a :
        Fin ((r + (0 + 0)).toNat + 1)) : ℕ) : ℤ) = (a : ℕ) + 0 := by simp
    simp only [h, ↓reduceDIte]
    simp only [zero_mul, Int.negOnePow_zero, one_smul, idDeg0, basedKron_eqToHom,
      eqToHom_trans_assoc]
    rfl
  · intro b _ hb
    have h : ¬ (((b : ℕ) : ℤ) = (a : ℕ) + 0) := fun h =>
      hb (Fin.ext (by simp only [Fin.coe_cast]; omega))
    simp only [h, ↓reduceDIte]
  · intro h; exact absurd (Finset.mem_univ _) h

end HSP.ChainModels
