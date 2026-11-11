import Mathlib
import HilbertSmithPaper.ChainModels.Grid.ChainModelDuality
import HilbertSmithPaper.ChainModels.Grid.Poincare.ChainModelAug
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.StrProdBlocks
import HilbertSmithPaper.ChainModels.Grid.Tensor.KronComposite
import HilbertSmithPaper.ChainModels.Grid.Tensor.KronDual
import HilbertSmithPaper.ChainModels.Grid.Tensor.BlockDecomposition
import HilbertSmithPaper.ChainModels.Grid.Cp2DimNeg
import HilbertSmithPaper.ChainModels.Grid.Cubical.GridFundamental
import HilbertSmithPaper.ChainModels.Grid.Cubical.GridAug
import HilbertSmithPaper.ChainModels.Grid.Cubical.CircleFundamental
import HilbertSmithPaper.ChainModels.Grid.Cubical.CircleAug
import HilbertSmithPaper.ChainModels.Grid.Cubical.CircleDimNeg

/-!
# The chain model is Poincaré: part 4

`ε φ_i(α) = α(z_i)` for every `α ∈ D_N^*`.

## Proof

For a product of structures, the block of `(φ ⊗ θ)_{0,k}` landing in the only summand
`C_0 ⊠ E_0` of degree `0` comes from the dual of `C_m ⊠ E_{m'}` with sign `+1`; so
`ε(φ ⊗ θ) = (εφ) ⊠ (εθ)` on that summand, which is the transpose of `z_C ⊠ z_E` when
`εφ = z_C^*` and `εθ = z_E^*`. Induct over the circle factors with circle duality (4), and
finish with `ε_P φ_P = e_4^*`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.ChainModels

open FreeQ DualCat

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

section Generic

variable {C E : ChainComplex FreeQ ℤ}

private lemma aug_block {m m' : ℤ} (φ : (StructureCx C).X m) (θ : (StructureCx E).X m')
    (augC : C.X 0 ⟶ (⟨1⟩ : FreeQ)) (augE : E.X 0 ⟶ (⟨1⟩ : FreeQ)) (zC : (⟨1⟩ : FreeQ) ⟶ C.X m)
    (zE : (⟨1⟩ : FreeQ) ⟶ E.X m') (hφ : φ ⟨(0, m), by ring⟩ ≫ augC = dualHom zC)
    (hθ : θ ⟨(0, m'), by ring⟩ ≫ augE = dualHom zE) {j v : ℤ} (hj : j = m) (hv : v = m')
    (h1 : 0 + j = m) (h2 : 0 + v = m') {W : FreeQ}
    (e : W = ⟨(dual (C.X j)).dim * (dual (E.X v)).dim⟩)
    (e' : W = ⟨(dual (C.X m)).dim * (dual (E.X m')).dim⟩) :
    eqToHom e ≫ basedKron (φ ⟨(0, j), h1⟩) (θ ⟨(0, v), h2⟩) ≫ basedKron augC augE =
      eqToHom e' ≫ basedKron (dualHom zC) (dualHom zE) := by
  subst hj hv e'
  simp only [eqToHom_refl, Category.id_comp]
  rw [basedKron_comp_basedKron, hφ, hθ]

private lemma dual_fund {X Y Z : FreeQ} {m : ℕ} (d : Fin m → ℕ) (q : Fin m) (zC : (⟨1⟩ : FreeQ) ⟶ X)
    (zE : (⟨1⟩ : FreeQ) ⟶ Y) (h : Y = Z) (hd : (⟨X.dim * Z.dim⟩ : FreeQ) = ⟨d q⟩) :
    dualHom (basedKron zC (zE ≫ eqToHom h) ≫ eqToHom hd ≫ blockInc d q) =
      blockProj d q ≫ eqToHom (by subst h; exact hd.symm) ≫
        basedKron (dualHom zC) (dualHom zE) := by
  subst h
  simp only [eqToHom_refl, Category.comp_id, dualHom_comp, dualHom_basedKron, dualHom_eqToHom]
  rw [Category.assoc]
  rfl

private lemma sum_blockProj_comp {m : ℕ} (d : Fin m → ℕ) {Y : FreeQ}
    (F : (⟨∑ i, d i⟩ : FreeQ) ⟶ Y) :
    F = ∑ a, blockProj d a ≫ blockInc d a ≫ F := by
  conv_lhs => rw [← Category.id_comp F, ← blockProj_comp_blockInc_sum d, Preadditive.sum_comp]
  simp only [Category.assoc]

private lemma aug_strProd (hE : ∀ q < 0, (E.X q).dim = 0) (q : ℕ) (m' k : ℤ) (hq : (q : ℤ) ≤ k)
    (hk : (q : ℤ) + m' = k) (φ : (StructureCx C).X q) (θ : (StructureCx E).X m')
    (augC : C.X 0 ⟶ (⟨1⟩ : FreeQ)) (augE : E.X 0 ⟶ (⟨1⟩ : FreeQ)) (zC : (⟨1⟩ : FreeQ) ⟶ C.X q)
    (zE : (⟨1⟩ : FreeQ) ⟶ E.X m') (hφ : φ ⟨(0, q), by ring⟩ ≫ augC = dualHom zC)
    (hθ : θ ⟨(0, m'), by ring⟩ ≫ augE = dualHom zE) :
    basedStrProd C E hE q m' k hk φ θ ⟨(0, k), by ring⟩ ≫
        blockProj (tensorSummandDim C E 0) ⟨0, Nat.succ_pos _⟩ ≫ basedKron augC augE =
      dualHom (basedKron zC (zE ≫ eqToHom (congrArg E.X (by omega : m' = k - (q : ℤ)))) ≫
        blockInc (tensorSummandDim C E k) ⟨q, by omega⟩) := by
  have hrk : (0 : ℤ) + k = k := by ring
  refine (sum_blockProj_comp (tensorSummandDim C E k) _).trans ?_
  refine (Finset.sum_eq_single (⟨q, by omega⟩ : Fin (k.toNat + 1)) ?_ ?_).trans ?_
  · intro a _ ha
    have hb := blockInc_comp_basedStrProd_comp_blockProj hE (q : ℤ) m' k hk φ θ 0 k hrk a
      ⟨0, Nat.succ_pos _⟩
    have hc : ¬ (((a : ℕ) : ℤ) =
        (q : ℤ) - (((⟨0, Nat.succ_pos _⟩ : Fin ((0 : ℤ).toNat + 1)) : ℕ) : ℤ)) :=
      fun h' => ha (Fin.ext (by simp only at h' ⊢; omega))
    simp only [hc, ↓reduceDIte] at hb
    refine (congrArg (blockProj _ a ≫ ·) (Eq.trans
      ((congrArg (_ ≫ ·) (Category.assoc _ _ _).symm).trans (Category.assoc _ _ _).symm)
      (congrArg (· ≫ basedKron augC augE) hb))).trans ?_
    simp only [zero_comp, comp_zero]
  · intro h; exact absurd (Finset.mem_univ _) h
  · have hz : E.X m' = E.X (k - (q : ℤ)) := congrArg E.X (by omega)
    have hR := dual_fund (tensorSummandDim C E k) ⟨q, by omega⟩ zC zE hz
      (rfl : (⟨(C.X q).dim * (E.X (k - (q : ℤ))).dim⟩ : FreeQ) =
        ⟨tensorSummandDim C E k ⟨q, by omega⟩⟩)
    rw [eqToHom_refl, Category.id_comp] at hR
    refine Eq.trans ?_ hR.symm
    congr 1
    refine (Eq.trans
      ((congrArg (_ ≫ ·) (Category.assoc _ _ _).symm).trans (Category.assoc _ _ _).symm)
      (congrArg (· ≫ basedKron augC augE) (blockInc_comp_basedStrProd_comp_blockProj hE (q : ℤ) m' k
        hk φ θ 0 k hrk ⟨q, by omega⟩ ⟨0, Nat.succ_pos _⟩))).trans ?_
    simp only [↓reduceDIte, Fin.val_mk, Nat.cast_zero, sub_zero, zero_mul, Int.negOnePow_zero,
      one_smul, Category.assoc]
    exact aug_block φ θ augC augE zC zE hφ hθ (by simp) (by simp) _ _ _ _

end Generic

private lemma unit_aug (k : ℕ) :
    unitStructure ⟨(0, 0), by ring⟩ ≫ gridAug k 0 = dualHom (gridFundamental k 0) := by
  refine Matrix.ext fun a b => ?_
  change (∑ c : Fin 1, (1 : ℚ) * 1) = 1
  simp

private lemma gridStructure_aug (k : ℕ) :
    ∀ n : ℕ, gridStructure k n ⟨(0, n), by ring⟩ ≫ gridAug k n = dualHom (gridFundamental k n)
  | 0 => unit_aug k
  | n + 1 => by
    have h4 := (circle_duality k).2.2.2.2.1
    exact aug_strProd (circleComplex_dim_neg k) n 1 ((n + 1 : ℕ) : ℤ) (by push_cast; omega)
      (by push_cast; ring) (gridStructure k n) (circlePhiSym k) (gridAug k n) (circleAug k)
      (gridFundamental k n) (circleFundamental k) (gridStructure_aug k n) (h4.1.trans h4.2.symm)

private lemma cp2_aug : cp2Structure ⟨(0, 4), by ring⟩ ≫ cp2Aug = dualHom cp2Fundamental := by
  refine Matrix.ext fun a b => ?_
  change (∑ c : Fin 1, (1 : ℚ) * 1) = 1
  simp

/-- *The chain model is Poincaré*, part 4: `ε φ_i(α) = α(z_i)` for every `α ∈ D_N^*`. -/
theorem chainModel_poincare_augmentation (A : LocalDatum p n D ρplus) (i : ℕ) :
    ((chainModelDuality A i).φ ⟨(0, (n + 4 : ℕ)), by ring⟩ ≫ chainModelAug A i =
      dualHom (chainModelFundamental A i)) :=
  aug_strProd cp2Complex_dim_neg n 4 ((n + 4 : ℕ) : ℤ) (by push_cast; omega) (by push_cast; ring)
    (gridStructure (meshSequence A i) n) cp2Structure (gridAug _ n) cp2Aug (gridFundamental _ n)
    cp2Fundamental (gridStructure_aug _ n) cp2_aug

end HSP.ChainModels
