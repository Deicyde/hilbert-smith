import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Tensor.BasedTensorHom
import HilbertSmithPaper.ChainModels.Grid.Tensor.IdDeg0
import HilbertSmithPaper.ChainModels.Grid.Tensor.Blocks.BlockExt
import HilbertSmithPaper.ChainModels.Grid.Tensor.Blocks.BlockExtraction
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.TensorHomTransportBlocks

/-!
# Differential of a tensor product

`d_{C ⊗ E} = d_C ⊗ 1 + 1 ⊗ d_E`, as tensors of graded maps of degrees `(-1, 0)` and `(0, -1)`, each followed by the identity transport of the target degree.

## Proof

Blockwise: the blocks of the differential are `d ⊠ 1` (to the summand `p - 1`) and `(-1)^p 1 ⊠ d` (to the summand `p`); the sign rule of the tensor gives the same blocks.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Kronecker

namespace HSP.ChainModels

open FreeQ DualCat

variable {C C' E E' : ChainComplex FreeQ ℤ}

private lemma d_eq_D (hE : ∀ q < 0, (E.X q).dim = 0) (r : ℤ) :
    (basedComplexTensor C E hE).d r (r - 1) =
      eqToHom (congrArg (basedComplexTensor C E hE).X (show r = r - 1 + 1 by ring)) ≫
        basedComplexTensorD C E (r - 1) := by
  change ChainComplex.of.d _ _ r (r - 1) = _
  rw [ChainComplex.of.d, dif_pos (show r = r - 1 + 1 by ring)]
  rfl

private lemma blockInc_comp_D_comp_blockProj (n : ℤ) (p : Fin ((n + 1).toNat + 1))
    (q : Fin (n.toNat + 1)) :
    blockInc (tensorSummandDim C E (n + 1)) p ≫ basedComplexTensorD C E n ≫
      blockProj (tensorSummandDim C E n) q = basedComplexTensorBlock C E n p q :=
  blockInc_comp_blockSum_comp_blockProj _ _ _ p q

private lemma blockInc_comp_D_transport {t s : ℤ} (h : t = s + 1) (p : Fin (t.toNat + 1))
    (q : Fin (s.toNat + 1)) :
    blockInc (tensorSummandDim C E t) p ≫
        (eqToHom (congrArg (basedComplexTensorObj C E) h) ≫ basedComplexTensorD C E s) ≫
      blockProj (tensorSummandDim C E s) q =
    eqToHom (by subst h; rfl) ≫ basedComplexTensorBlock C E s (Fin.cast (by rw [h]) p) q := by
  subst h
  simp only [eqToHom_refl, Category.id_comp, Fin.cast_eq_self]
  exact blockInc_comp_D_comp_blockProj s p q

private lemma blk_add {m m' : ℕ} {d : Fin m → ℕ} {d' : Fin m' → ℕ} (p : Fin m) (q : Fin m')
    (F G : (⟨∑ i, d i⟩ : FreeQ) ⟶ ⟨∑ i, d' i⟩) :
    blockInc d p ≫ (F + G) ≫ blockProj d' q =
      blockInc d p ≫ F ≫ blockProj d' q + blockInc d p ≫ G ≫ blockProj d' q := by
  rw [Preadditive.add_comp, Preadditive.comp_add]

private lemma negOnePow_neg_smul {X Y : FreeQ} (n : ℕ) (x : X ⟶ Y) :
    ((-1) * (n : ℤ)).negOnePow • x = ((-1 : ℚ) ^ n) • x := by
  rw [neg_one_mul, Int.negOnePow_neg, Units.smul_def, ← Int.cast_smul_eq_zsmul ℚ,
    Int.cast_negOnePow_natCast]

private lemma kron_d_transport_left {A B : ℤ → FreeQ} (F : ∀ i j, A i ⟶ A j)
    {a a' b b' c c' e e' : ℤ} (ha : a = a') (hb : b = b') (hc : c = e) (hc' : c' = e')
    (hcc : c = c')
    (h0 : (⟨(A a).dim * (B c).dim⟩ : FreeQ) = ⟨(A a').dim * (B c').dim⟩)
    (h1 : (⟨(A b).dim * (B e).dim⟩ : FreeQ) = ⟨(A b').dim * (B e').dim⟩) :
    eqToHom h0 ≫ basedKron (F a' b') (eqToHom (congrArg B hc')) =
      basedKron (F a b) (eqToHom (congrArg B hc)) ≫ eqToHom h1 := by
  subst ha hb hcc hc hc'; simp

private lemma kron_d_transport_right {A B : ℤ → FreeQ} (G : ∀ i j, B i ⟶ B j)
    {a a' b b' c c' e e' : ℤ} (ha : a = a') (hb : b = b') (hc : c = e) (hc' : c' = e')
    (hcc : c = c')
    (h0 : (⟨(A c).dim * (B a).dim⟩ : FreeQ) = ⟨(A c').dim * (B a').dim⟩)
    (h1 : (⟨(A e).dim * (B b).dim⟩ : FreeQ) = ⟨(A e').dim * (B b').dim⟩) :
    eqToHom h0 ≫ basedKron (eqToHom (congrArg A hc')) (G a' b') =
      basedKron (eqToHom (congrArg A hc)) (G a b) ≫ eqToHom h1 := by
  subst ha hb hcc hc hc'; simp

theorem basedComplexTensor_d_eq (hE : ∀ q < 0, (E.X q).dim = 0) (r : ℤ) :
    (basedComplexTensor C E hE).d r (r - 1) =
      basedTensorHom hE hE (-1) 0 (fun t => C.d t (t + -1)) (idDeg0 E) r ≫
          eqToHom (congrArg (basedComplexTensor C E hE).X (by ring)) +
        basedTensorHom hE hE 0 (-1) (idDeg0 C) (fun t => E.d t (t + -1)) r ≫
          eqToHom (congrArg (basedComplexTensor C E hE).X (by ring)) := by
  refine block_ext fun p q => ?_
  rw [d_eq_D]
  refine (blockInc_comp_D_transport (show r = r - 1 + 1 by ring) p q).trans ?_
  refine Eq.trans ?_ (blk_add p q _ _).symm
  refine Eq.trans ?_ (congrArg₂ (· + ·)
    (blockInc_comp_basedTensorHom_comp_eqToHom_comp_blockProj hE hE (-1) 0 _ _ r (r - 1) (by ring) p q).symm
    (blockInc_comp_basedTensorHom_comp_eqToHom_comp_blockProj hE hE 0 (-1) _ _ r (r - 1) (by ring) p q).symm)
  simp only [basedComplexTensorBlock, Fin.coe_cast]
  by_cases h1 : (q : ℕ) + 1 = (p : ℕ)
  · have hA : (((q : ℕ) : ℤ) = (p : ℕ) + -1) = True := eq_true (by omega)
    have hB : ¬ ((q : ℕ) : ℤ) = (p : ℕ) + 0 := by omega
    have h1' : ((q : ℕ) + 1 = (p : ℕ)) = True := eq_true h1
    simp only [h1', hA, hB, ↓reduceDIte, zero_mul, Int.negOnePow_zero,
      one_smul, idDeg0, HomologicalComplex.XIsoOfEq, eqToIso.hom]
    refine Eq.trans ?_ (add_zero _).symm
    exact kron_d_transport_left C.d rfl (by omega) (by ring) (by simp only [Fin.coe_cast]; omega)
      (by simp only [Fin.coe_cast]; omega) _ _
  · by_cases h2 : (q : ℕ) = (p : ℕ)
    · have hA : ¬ ((q : ℕ) : ℤ) = (p : ℕ) + -1 := by omega
      have hB : (((q : ℕ) : ℤ) = (p : ℕ) + 0) = True := eq_true (by omega)
      have h2' : ((q : ℕ) = (p : ℕ)) = True := eq_true h2
      simp only [h1, h2', hA, hB, ↓reduceDIte, idDeg0,
        HomologicalComplex.XIsoOfEq, eqToIso.hom, Linear.comp_smul, negOnePow_neg_smul]
      refine Eq.trans ?_ (zero_add _).symm
      congr 1
      exact kron_d_transport_right E.d (by simp only [Fin.coe_cast]; omega) (by omega)
        (by ring) (by omega) rfl _ _
    · have hA : ¬ ((q : ℕ) : ℤ) = (p : ℕ) + -1 := by omega
      have hB : ¬ ((q : ℕ) : ℤ) = (p : ℕ) + 0 := by omega
      simp only [h1, h2, hA, hB, ↓reduceDIte, comp_zero]
      simp only [add_zero]

end HSP.ChainModels
