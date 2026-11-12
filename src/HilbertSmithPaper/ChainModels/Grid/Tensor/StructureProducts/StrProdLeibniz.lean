import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.StrProdBlocks
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.BlockDual
import HilbertSmithPaper.ChainModels.Grid.Tensor.KronDual
import HilbertSmithPaper.ChainModels.Grid.Tensor.KronComposite
import HilbertSmithPaper.ChainModels.Grid.Tensor.KronAddLeft
import HilbertSmithPaper.ChainModels.Grid.Tensor.KronAddRight
import HilbertSmithPaper.ChainModels.Grid.Tensor.KronSmulLeft
import HilbertSmithPaper.ChainModels.Grid.Tensor.KronSmulRight
import HilbertSmithPaper.ChainModels.Grid.Tensor.BlockExt
import HilbertSmithPaper.ChainModels.Grid.Tensor.BlockComp
import HilbertSmithPaper.ChainModels.Grid.Tensor.BlockExtraction

/-!
# Leibniz rule for products of structures

`∂(φ ⊗ θ) = ∂φ ⊗ θ + (-1)^m φ ⊗ ∂θ` for `φ ∈ M(C)_m`.

## Proof

Blockwise, from the dual of the summand `a` of degree `s` to the summand `p` of degree `r`: if `a = m - 1 - p` only the paths through `C_{p+1} ⊠ E_{r-p}` (via `d ⊠ 1`) and through the dual of `C_{a+1} ⊠ E_{s-a}` (via `d^* ⊠ 1`) contribute, matching the two terms of `∂φ`; if `a = m - p` only the paths via `1 ⊠ d` and `1 ⊠ d^*` contribute, matching the two terms of `∂θ`; otherwise every path vanishes.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Kronecker

namespace HSP.ChainModels

open FreeQ DualCat

variable {C E : ChainComplex FreeQ ℤ}

variable (hE : ∀ q < 0, (E.X q).dim = 0)

private lemma hom_ext_dim_zero_target {X Y : FreeQ} (f g : X ⟶ Y) (h : Y.dim = 0) : f = g :=
  Matrix.ext fun i _ => (Fin.cast h i).elim0

private lemma hom_ext_dim_zero_source {X Y : FreeQ} (f g : X ⟶ Y) (h : X.dim = 0) : f = g :=
  Matrix.ext fun _ j => (Fin.cast h j).elim0

private lemma blk_dF {n₁ n₂ n₂' n₃ : ℕ} {d₁ : Fin n₁ → ℕ} {d₂ : Fin n₂ → ℕ} {d₂' : Fin n₂' → ℕ}
    {d₃ : Fin n₃ → ℕ} (X : (⟨∑ i, d₁ i⟩ : FreeQ) ⟶ ⟨∑ i, d₂ i⟩)
    (Y : (⟨∑ i, d₂ i⟩ : FreeQ) ⟶ ⟨∑ i, d₃ i⟩)
    (Z : (⟨∑ i, d₁ i⟩ : FreeQ) ⟶ ⟨∑ i, d₂' i⟩) (W : (⟨∑ i, d₂' i⟩ : FreeQ) ⟶ ⟨∑ i, d₃ i⟩)
    (u : ℤˣ) (a : Fin n₁) (p : Fin n₃) :
    blockInc d₁ a ≫ (X ≫ Y + u • (Z ≫ W)) ≫ blockProj d₃ p =
      ∑ b, (blockInc d₁ a ≫ X ≫ blockProj d₂ b) ≫ (blockInc d₂ b ≫ Y ≫ blockProj d₃ p) +
        u • ∑ b, (blockInc d₁ a ≫ Z ≫ blockProj d₂' b) ≫ (blockInc d₂' b ≫ W ≫ blockProj d₃ p) := by
  rw [Preadditive.add_comp, Preadditive.comp_add, Linear.units_smul_comp, Linear.comp_units_smul,
    block_comp, block_comp]

private lemma blk_add_smul {n₁ n₃ : ℕ} {d₁ : Fin n₁ → ℕ} {d₃ : Fin n₃ → ℕ}
    (X Y : (⟨∑ i, d₁ i⟩ : FreeQ) ⟶ ⟨∑ i, d₃ i⟩) (u : ℤˣ) (a : Fin n₁) (p : Fin n₃) :
    blockInc d₁ a ≫ (X + u • Y) ≫ blockProj d₃ p =
      blockInc d₁ a ≫ X ≫ blockProj d₃ p + u • (blockInc d₁ a ≫ Y ≫ blockProj d₃ p) := by
  rw [Preadditive.add_comp, Preadditive.comp_add, Linear.units_smul_comp, Linear.comp_units_smul]

private lemma blk_d (n : ℤ) (b : Fin ((n + 1).toNat + 1)) (p : Fin (n.toNat + 1)) :
    blockInc (tensorSummandDim C E (n + 1)) b ≫
      ((basedComplexTensor C E hE).d (n + 1) n :
        (⟨∑ i, tensorSummandDim C E (n + 1) i⟩ : FreeQ) ⟶ ⟨∑ i, tensorSummandDim C E n i⟩) ≫
      blockProj (tensorSummandDim C E n) p = basedComplexTensorBlock C E n b p := by
  rw [basedComplexTensor_d]
  exact blockInc_comp_blockSum_comp_blockProj _ _ _ b p

private lemma blk_dual_d (n : ℤ) (a : Fin (n.toNat + 1)) (b : Fin ((n + 1).toNat + 1)) :
    blockInc (tensorSummandDim C E n) a ≫
      (dualHom ((basedComplexTensor C E hE).d (n + 1) n) :
        (⟨∑ i, tensorSummandDim C E n i⟩ : FreeQ) ⟶ ⟨∑ i, tensorSummandDim C E (n + 1) i⟩) ≫
      blockProj (tensorSummandDim C E (n + 1)) b = dualHom (basedComplexTensorBlock C E n b a) := by
  rw [← blk_d hE n b a]
  exact blockInc_comp_dualHom_comp_blockProj _ _ _ b a

private lemma leib_C1 {m m' : ℤ} (φ : (StructureCx C).X m) (θ : (StructureCx E).X m')
    {i i' j j' u v v' c w : ℤ} (hi : i = i') (hj : j = j') (hu : u = w) (hv : v = v')
    (hij : i + j = m) (hij' : i' + j' = m) (huv : u + v = m') (hwv : w + v' = m')
    {W : FreeQ} (e : W = ⟨(dual (C.X j)).dim * (dual (E.X v)).dim⟩)
    (e' : W = ⟨(dual (C.X j')).dim * (dual (E.X v')).dim⟩) (hX : E.X u = E.X w) :
    eqToHom e ≫ basedKron (φ ⟨(i, j), hij⟩) (θ ⟨(u, v), huv⟩) ≫ basedKron (C.d i c) (eqToHom hX) =
      eqToHom e' ≫ basedKron (φ ⟨(i', j'), hij'⟩ ≫ C.d i' c) (θ ⟨(w, v'), hwv⟩) := by
  subst hi hj hu hv e
  simp only [eqToHom_refl, Category.id_comp]
  rw [basedKron_comp_basedKron, Category.comp_id]

private lemma leib_C2 {m m' : ℤ} (φ : (StructureCx C).X m) (θ : (StructureCx E).X m')
    {i i' c c' i2 j2 u v y1 y2 : ℤ} (hi : i = i') (hc : c = c') (hj : j2 = i') (hy2 : y2 = v)
    (hy1 : y1 = v) (hij : i2 + j2 = m) (hij' : i2 + i' = m) (huv : u + v = m')
    (hX : dual (E.X y1) = dual (E.X y2))
    (e : (⟨(dual (C.X i)).dim * (dual (E.X y2)).dim⟩ : FreeQ) =
      ⟨(dual (C.X j2)).dim * (dual (E.X v)).dim⟩)
    {W : FreeQ} (hW : W = ⟨(dual (C.X c)).dim * (dual (E.X y1)).dim⟩)
    (e' : W = ⟨(dual (C.X c')).dim * (dual (E.X v)).dim⟩) :
    eqToHom hW ≫ basedKron (dualHom (C.d i c)) (eqToHom hX) ≫ eqToHom e ≫
        basedKron (φ ⟨(i2, j2), hij⟩) (θ ⟨(u, v), huv⟩) =
      eqToHom e' ≫ basedKron (dualHom (C.d i' c') ≫ φ ⟨(i2, i'), hij'⟩) (θ ⟨(u, v), huv⟩) := by
  subst hi hc hj hy2 hy1 hW
  simp only [eqToHom_refl, Category.id_comp]
  rw [basedKron_comp_basedKron, Category.id_comp]

private lemma leib_E1 {m m' : ℤ} (φ : (StructureCx C).X m) (θ : (StructureCx E).X m')
    {i j j' u u' v v' c w : ℤ} (hc : i = c) (hj : j = j') (hu : u = u') (hv : v = v')
    (hij : i + j = m) (hcj : c + j' = m) (huv : u + v = m') (huv' : u' + v' = m')
    {W : FreeQ} (e : W = ⟨(dual (C.X j)).dim * (dual (E.X v)).dim⟩)
    (e' : W = ⟨(dual (C.X j')).dim * (dual (E.X v')).dim⟩) (hX : C.X i = C.X c) :
    eqToHom e ≫ basedKron (φ ⟨(i, j), hij⟩) (θ ⟨(u, v), huv⟩) ≫ basedKron (eqToHom hX) (E.d u w) =
      eqToHom e' ≫ basedKron (φ ⟨(c, j'), hcj⟩) (θ ⟨(u', v'), huv'⟩ ≫ E.d u' w) := by
  subst hc hj hu hv e
  simp only [eqToHom_refl, Category.id_comp]
  rw [basedKron_comp_basedKron, Category.comp_id]

private lemma leib_E2 {m m' : ℤ} (φ : (StructureCx C).X m) (θ : (StructureCx E).X m')
    {c c2 i2 j2 u v y z z' : ℤ} (hc : c = j2) (hc2 : c2 = j2) (hy : y = v) (hz : z = z')
    (hij : i2 + j2 = m) (huv : u + v = m') (hC : dual (C.X c) = dual (C.X c2))
    (e : (⟨(dual (C.X c2)).dim * (dual (E.X y)).dim⟩ : FreeQ) =
      ⟨(dual (C.X j2)).dim * (dual (E.X v)).dim⟩)
    {W : FreeQ} (hW : W = ⟨(dual (C.X c)).dim * (dual (E.X z)).dim⟩)
    (e' : W = ⟨(dual (C.X j2)).dim * (dual (E.X z')).dim⟩) :
    eqToHom hW ≫ basedKron (eqToHom hC) (dualHom (E.d y z)) ≫ eqToHom e ≫
        basedKron (φ ⟨(i2, j2), hij⟩) (θ ⟨(u, v), huv⟩) =
      eqToHom e' ≫ basedKron (φ ⟨(i2, j2), hij⟩) (dualHom (E.d v z') ≫ θ ⟨(u, v), huv⟩) := by
  subst hc hc2 hy hz hW
  simp only [eqToHom_refl, Category.id_comp]
  rw [basedKron_comp_basedKron, Category.id_comp]

private lemma pow_smul_eq {X Y : FreeQ} (n : ℕ) (x : X ⟶ Y) :
    ((-1 : ℚ) ^ n) • x = ((n : ℤ)).negOnePow • x := by
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_negOnePow_natCast]

theorem basedStrProd_d (m m' k : ℤ) (hk : m + m' = k) (φ : (StructureCx C).X m)
    (θ : (StructureCx E).X m') :
    (StructureCx (basedComplexTensor C E hE)).d k (k - 1) (basedStrProd C E hE m m' k hk φ θ) =
      basedStrProd C E hE (m - 1) m' (k - 1) (by omega) ((StructureCx C).d m (m - 1) φ) θ +
        m.negOnePow • basedStrProd C E hE m (m' - 1) (k - 1) (by omega) φ
          ((StructureCx E).d m' (m' - 1) θ) := by
  have hdu : ∀ {X Y : FreeQ} (u : ℤˣ) (f : X ⟶ Y), dualHom (u • f) = u • dualHom f :=
    fun {X Y} u f => by
      rw [Units.smul_def, Units.smul_def]
      exact (AddMonoidHom.mk' (dualHom (M := X) (N := Y)) dualHom_add).map_zsmul (u : ℤ) f
  funext x
  refine block_ext fun a p => ?_
  have h := x.2
  by_cases hr : x.1.1 < 0
  · refine hom_ext_dim_zero_target _ _ ?_
    change (C.X (p : ℕ)).dim * (E.X (x.1.1 - (p : ℕ))).dim = 0
    rw [hE _ (by omega), mul_zero]
  by_cases hs : x.1.2 < 0
  · refine hom_ext_dim_zero_source _ _ ?_
    change (C.X (a : ℕ)).dim * (E.X (x.1.2 - (a : ℕ))).dim = 0
    rw [hE _ (by omega), mul_zero]
  rw [StructureCx.d_apply _ k (k - 1) _ x.1.1 x.1.2 x.2 (x.1.1 + 1) (x.1.2 + 1) (by omega)
    (by omega)]
  refine (blk_dF _ _ _ _ _ a p).trans ?_
  rw [Pi.add_apply, Pi.smul_apply]
  refine Eq.trans ?_ (blk_add_smul _ _ _ a p).symm
  have h1 : x.1.1 + 1 + x.1.2 = k := by omega
  have h2 : x.1.1 + (x.1.2 + 1) = k := by omega
  have h3 : m - 1 + m' = k - 1 := by omega
  have h4 : m + (m' - 1) = k - 1 := by omega
  refine Eq.trans (congrArg₂ (fun X Y => X + x.1.1.negOnePow • Y)
    (Finset.sum_congr rfl fun b _ => congrArg₂ (· ≫ ·)
      (blockInc_comp_basedStrProd_comp_blockProj hE m m' k hk φ θ (x.1.1 + 1) x.1.2 h1 a b)
      (blk_d hE x.1.1 b p))
    (Finset.sum_congr rfl fun b _ => congrArg₂ (· ≫ ·) (blk_dual_d hE x.1.2 a b)
      (blockInc_comp_basedStrProd_comp_blockProj hE m m' k hk φ θ x.1.1 (x.1.2 + 1) h2 b p))) ?_
  refine Eq.trans ?_ (congrArg₂ (fun X Y => X + m.negOnePow • Y)
    (blockInc_comp_basedStrProd_comp_blockProj hE (m - 1) m' (k - 1) h3 _ θ x.1.1 x.1.2 x.2 a p)
    (blockInc_comp_basedStrProd_comp_blockProj hE m (m' - 1) (k - 1) h4 φ _ x.1.1 x.1.2 x.2
      a p)).symm
  rw [StructureCx.d_apply C m (m - 1) φ (p : ℕ) (m - 1 - (p : ℕ)) (by ring) ((p : ℕ) + 1)
      (m - (p : ℕ)) (by ring) (by ring),
    StructureCx.d_apply E m' (m' - 1) θ (x.1.1 - (p : ℕ)) (m' - 1 - (x.1.1 - (p : ℕ))) (by ring)
      (x.1.1 - (p : ℕ) + 1) (m' - (x.1.1 - (p : ℕ))) (by ring) (by ring)]
  by_cases c1 : ((a : ℕ) : ℤ) = m - 1 - (p : ℕ)
  · -- the summand `C_{p+1} ⊠ E_{r-p}`, through `d ⊠ 1`
    have c2 : ¬ ((a : ℕ) : ℤ) = m - (p : ℕ) := by omega
    have c1' : (((a : ℕ) : ℤ) = m - 1 - (p : ℕ)) = True := eq_true c1
    simp only [c1', c2, ↓reduceDIte, smul_zero, add_zero]
    rw [Finset.sum_eq_single (⟨(p : ℕ) + 1, by omega⟩ : Fin ((x.1.1 + 1).toNat + 1)),
      Finset.sum_eq_single (⟨(a : ℕ) + 1, by omega⟩ : Fin ((x.1.2 + 1).toNat + 1))]
    · have e1 : (((a : ℕ) : ℤ) = m - (((p : ℕ) + 1 : ℕ) : ℤ)) = True :=
        eq_true (by push_cast; omega)
      have e2 : ((((a : ℕ) + 1 : ℕ) : ℤ) = m - ((p : ℕ) : ℤ)) = True :=
        eq_true (by push_cast; omega)
      simp only [e1, e2, ↓reduceDIte, basedComplexTensorBlock, Fin.val_mk,
        HomologicalComplex.XIsoOfEq,
        eqToIso.hom, dualHom_basedKron, dualHom_eqToHom, Linear.units_smul_comp,
        Linear.comp_units_smul, Category.assoc, basedKron_add_left, basedKron_units_smul_left,
        Preadditive.comp_add, smul_add, smul_smul]
      congr 1
      · congr 1
        · rw [Int.negOnePow_eq_iff]
          push_cast
          exact ⟨x.1.1 - (p : ℕ), by ring⟩
        · exact leib_C1 φ θ (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)
            (by push_cast; ring) _ _ _ _ _ _ _
      · congr 1
        · rw [← Int.negOnePow_add, ← Int.negOnePow_add, Int.negOnePow_eq_iff]
          exact ⟨x.1.1 - (p : ℕ), by ring⟩
        · refine Eq.trans (Category.id_comp _).symm ?_
          exact leib_C2 φ θ (by push_cast; omega) (by omega) rfl (by push_cast; omega)
            (by push_cast; omega) _ _ _ _ _ rfl _
    · intro b _ hb
      have hb' : ¬ (((b : ℕ) : ℤ) = m - (p : ℕ)) := fun h' => hb (Fin.ext (by simp only; omega))
      simp only [hb', ↓reduceDIte, comp_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro b _ hb
      have hb' : ¬ (((a : ℕ) : ℤ) = m - (b : ℕ)) := fun h' => hb (Fin.ext (by simp only; omega))
      simp only [hb', ↓reduceDIte, zero_comp]
    · intro h; exact absurd (Finset.mem_univ _) h
  · by_cases c2 : ((a : ℕ) : ℤ) = m - (p : ℕ)
    · -- the summand `C_p ⊠ E_{r+1-p}`, through `1 ⊠ d`
      have c2' : (((a : ℕ) : ℤ) = m - (p : ℕ)) = True := eq_true c2
      simp only [c1, c2', ↓reduceDIte, zero_add]
      rw [Finset.sum_eq_single (⟨(p : ℕ), by omega⟩ : Fin ((x.1.1 + 1).toNat + 1)),
        Finset.sum_eq_single (⟨(a : ℕ), by omega⟩ : Fin ((x.1.2 + 1).toNat + 1))]
      · have hp1 : ¬ ((p : ℕ) + 1 = (p : ℕ)) := by omega
        have ha1 : ¬ ((a : ℕ) + 1 = (a : ℕ)) := by omega
        simp only [c2', hp1, ha1, ↓reduceDIte, basedComplexTensorBlock, Fin.val_mk,
          HomologicalComplex.XIsoOfEq, eqToIso.hom, dualHom_basedKron, dualHom_eqToHom,
          pow_smul_eq, hdu, Linear.units_smul_comp, Linear.comp_units_smul,
          Category.assoc, basedKron_add_right, basedKron_units_smul_right, Preadditive.comp_add,
          smul_add, smul_smul]
        congr 1
        · congr 1
          · simp only [← Int.negOnePow_add]
            rw [Int.negOnePow_eq_iff]
            exact ⟨((p : ℕ) : ℤ), by ring⟩
          · exact leib_E1 φ θ rfl rfl (by ring) (by ring) _ _ _ _ _ _ _
        · congr 1
          · simp only [← Int.negOnePow_add]
            rw [Int.negOnePow_eq_iff]
            exact ⟨0, by linear_combination c2⟩
          · refine Eq.trans (Category.id_comp _).symm ?_
            exact leib_E2 φ θ (by omega) (by omega) (by dsimp only; omega) (by dsimp only; omega)
              _ _ _ _ rfl _
      · intro b _ hb
        have hb' : ¬ (((b : ℕ) : ℤ) = m - (p : ℕ)) := fun h' => hb (Fin.ext (by simp only; omega))
        simp only [hb', ↓reduceDIte, comp_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
      · intro b _ hb
        have hb' : ¬ (((a : ℕ) : ℤ) = m - (b : ℕ)) := fun h' => hb (Fin.ext (by simp only; omega))
        simp only [hb', ↓reduceDIte, zero_comp]
      · intro h; exact absurd (Finset.mem_univ _) h
    · -- no summand contributes
      simp only [c1, c2, ↓reduceDIte, smul_zero, add_zero]
      rw [Finset.sum_eq_zero, Finset.sum_eq_zero, smul_zero, add_zero]
      · intro b _
        by_cases hb : ((b : ℕ) : ℤ) = m - (p : ℕ)
        · have h1' : ¬ ((a : ℕ) + 1 = (b : ℕ)) := by omega
          have h2' : ¬ ((a : ℕ) = (b : ℕ)) := by omega
          simp only [basedComplexTensorBlock, h1', h2', ↓reduceDIte, dualHom_zero, zero_comp]
        · simp only [hb, ↓reduceDIte, comp_zero]
      · intro b _
        by_cases hb : ((a : ℕ) : ℤ) = m - (b : ℕ)
        · have h1' : ¬ ((p : ℕ) + 1 = (b : ℕ)) := by omega
          have h2' : ¬ ((p : ℕ) = (b : ℕ)) := by omega
          simp only [basedComplexTensorBlock, h1', h2', ↓reduceDIte, comp_zero]
        · simp only [hb, ↓reduceDIte, zero_comp]

end HSP.ChainModels
