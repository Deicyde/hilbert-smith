import Mathlib
import HilbertSmithPaper.ChainModels.Grid.ChainModelDuality
import HilbertSmithPaper.ChainModels.Grid.Poincare.ChainModelHDual
import HilbertSmithPaper.ChainModels.Grid.Poincare.ChainModelH
import HilbertSmithPaper.ChainModels.Grid.Poincare.GridFactor.GridH
import HilbertSmithPaper.ChainModels.Grid.Poincare.GridFactor.GridHDual
import HilbertSmithPaper.ChainModels.Grid.Poincare.GridFactor.CircleA
import HilbertSmithPaper.ChainModels.Grid.Poincare.GridFactor.CircleADual
import HilbertSmithPaper.ChainModels.Grid.Poincare.GridFactor.GridDimNeg
import HilbertSmithPaper.ChainModels.Grid.Poincare.GridFactor.GridInverseRight
import HilbertSmithPaper.ChainModels.Grid.Poincare.Cp2Inverse
import HilbertSmithPaper.ChainModels.Grid.Poincare.ChainModelInverseChainMap
import HilbertSmithPaper.ChainModels.Grid.Poincare.ChainModelInverseExact
import HilbertSmithPaper.ChainModels.Grid.Poincare.ChainModelHomotopy
import HilbertSmithPaper.ChainModels.Grid.Poincare.ChainModelStructureUCycle
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.StrProdTensorDualProd
import HilbertSmithPaper.LTheory.Base.Complexes.CycleChainMap
import HilbertSmithPaper.LTheory.Base.Complexes.DualComplex

/-!
# The chain-model dual homotopy

`b_i φ_i - 1 = dH'_i + H'_i d` on `D_i^{N-*}`, where `d_r = (-1)^r d^*`.

## Proof

Conjugation: `H'_i = b_i H_i φ_i^u`, from the composite of a product of structures, a tensor and a
product of duality maps, by induction over the circle factors (`A' = bAφ`, `K' = bKφ` and
`1 = b1φ` from circle duality (1)). Then, with `bφ^u = 1`, `φ^u b = 1`, `b` and `φ^u` chain maps,
`bφ - 1 = b(φb - 1)φ^u = b(dH + Hd)φ^u = dH' + H'd`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.ChainModels

open FreeQ DualCat

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- Transport of a family of maps between dual complexes along an equality of indices. -/
private lemma famD_eqToHom {X Y : ℤ → FreeQ} (h : ∀ a, X a ⟶ Y a) {a b : ℤ} (e : a = b) :
    eqToHom (congrArg X e) ≫ h b = h a ≫ eqToHom (congrArg Y e) := by
  subst e; simp

/-- `H'^{(n)} = b H^{(n)} φ^u_n` on the grid. -/
private lemma gridH'_conj (k : ℕ) : ∀ (n : ℕ) (r : ℤ),
    gridH' k n r = gridStructureU k n ⟨(r, (n : ℤ) - r), by ring⟩ ≫ gridH k n r ≫
      gridDualMap k n (r + 1)
  | 0, r => by simp [gridH, gridH']
  | n + 1, r => by
    have L1 := basedStrProd_comp_basedTensorHom_comp_basedDualProd (circleComplex_dim_neg k)
      (gridComplex_dim_neg k n) n 1 ((n + 1 : ℕ) : ℤ) (by push_cast; ring) (gridStructureU k n)
      (circlePhi k) 1 0 (gridH k n) (circleA k) (gridDualMap k n) (circleB k) r (r + 1) (by ring)
    have L2 := basedStrProd_comp_basedTensorHom_comp_basedDualProd (circleComplex_dim_neg k)
      (gridComplex_dim_neg k n) n 1 ((n + 1 : ℕ) : ℤ) (by push_cast; ring) (gridStructureU k n)
      (circlePhi k) 0 1 (idDeg0 (gridComplex k n)) (circleK k) (gridDualMap k n) (circleB k) r
      (r + 1) (by ring)
    have hF1 : (fun t => gridStructureU k n ⟨(t, (n : ℤ) - t), by ring⟩ ≫ gridH k n t ≫
        gridDualMap k n (t + 1)) = gridH' k n := funext fun t => (gridH'_conj k n t).symm
    have hG1 : (fun t => circlePhi k ⟨(t, 1 - t), by ring⟩ ≫ circleA k t ≫ circleB k (t + 0)) =
        circleA' k := funext fun t => by
      simp only [circleA, circleA', Category.assoc]
      rw [famD_eqToHom (fun t => circleB k t) (add_zero t).symm, ← Category.assoc,
        ← Category.assoc, ((circle_duality k).1.2 t).1, Category.id_comp]
    have hF2 : (fun t => gridStructureU k n ⟨(t, (n : ℤ) - t), by ring⟩ ≫
        idDeg0 (gridComplex k n) t ≫ gridDualMap k n (t + 0)) = idDualDeg0 (gridComplex k n) n :=
      funext fun t => by
        simp only [idDeg0]
        rw [famD_eqToHom (fun t => gridDualMap k n t) (add_zero t).symm, ← Category.assoc,
          gridStructureU_comp_gridDualMap k n t, Category.id_comp]
        rfl
    have hG2 : (fun t => circlePhi k ⟨(t, 1 - t), by ring⟩ ≫ circleK k t ≫ circleB k (t + 1)) =
        circleK' k := funext fun t => by
      simp only [circleK, circleK', Linear.smul_comp, Linear.comp_smul, Category.assoc]
      rw [← Category.assoc (circlePhi k _), ((circle_duality k).1.2 t).1, Category.id_comp]
    rw [hF1, hG1] at L1
    rw [hF2, hG2] at L2
    have key : ∀ {P Q R S : FreeQ} (u : P ⟶ Q) (x y : Q ⟶ R) (v : R ⟶ S),
        u ≫ (x + y) ≫ v = u ≫ x ≫ v + u ≫ y ≫ v := by
      intros; rw [Preadditive.add_comp, Preadditive.comp_add]
    symm
    exact (key _ (basedTensorHom (circleComplex_dim_neg k) (circleComplex_dim_neg k) 1 0 (gridH k n)
        (circleA k) r ≫ eqToHom (congrArg (basedComplexTensor (gridComplex k n) (circleComplex k)
          (circleComplex_dim_neg k)).X (show r + (1 + 0) = r + 1 by ring)))
      (basedTensorHom (circleComplex_dim_neg k) (circleComplex_dim_neg k) 0 1
        (idDeg0 (gridComplex k n)) (circleK k) r ≫ eqToHom (congrArg (basedComplexTensor
          (gridComplex k n) (circleComplex k) (circleComplex_dim_neg k)).X
            (show r + (0 + 1) = r + 1 by ring))) _).trans
      (congrArg₂ (· + ·) ((congrArg (fun x => _ ≫ x) (Category.assoc _ _ _)).trans L1)
        ((congrArg (fun x => _ ≫ x) (Category.assoc _ _ _)).trans L2))

/-- `H'_i = b_i H_i φ_i^u` on the chain model. -/
private lemma chainModelH'_conj (A : LocalDatum p n D ρplus) (i : ℕ) (r : ℤ) :
    chainModelH' A i r = chainModelStructureU A i ⟨(r, (n + 4 : ℕ) - r), by ring⟩ ≫
      chainModelH A i r ≫ (chainModelDuality A i).b (r + 1) := by
  have L := basedStrProd_comp_basedTensorHom_comp_basedDualProd cp2Complex_dim_neg
    (gridComplex_dim_neg _ n) n 4 ((n + 4 : ℕ) : ℤ) (by push_cast; ring)
    (gridStructureU (meshSequence A i) n) cp2Structure 1 0 (gridH (meshSequence A i) n)
    (idDeg0 cp2Complex) (gridDualMap (meshSequence A i) n) cp2Inverse.f r (r + 1) (by ring)
  have hF : (fun t => gridStructureU (meshSequence A i) n ⟨(t, (n : ℤ) - t), by ring⟩ ≫
      gridH (meshSequence A i) n t ≫ gridDualMap (meshSequence A i) n (t + 1)) =
      gridH' (meshSequence A i) n := funext fun t => (gridH'_conj _ n t).symm
  have hG : (fun t => cp2Structure ⟨(t, 4 - t), by ring⟩ ≫ idDeg0 cp2Complex t ≫
      cp2Inverse.f (t + 0)) = idDualDeg0 cp2Complex 4 := funext fun t => by
    simp only [idDeg0]
    rw [famD_eqToHom (fun t => cp2Inverse.f t) (add_zero t).symm, ← Category.assoc,
      (cp2Inverse_comp_cp2Structure t).2, Category.id_comp]
    rfl
  rw [hF, hG] at L
  exact ((congrArg (fun x => _ ≫ x) (Category.assoc _ _ _)).trans L).symm

/-- *The chain-model dual homotopy*: `b_i φ_i - 1 = dH'_i + H'_i d` on `D_i^{N-*}`,
where `d_r = (-1)^r d^*`. -/
theorem chainModel_dual_homotopy (A : LocalDatum p n D ρplus) (i : ℕ) :
    ∀ r : ℤ, (chainModelDuality A i).φ ⟨(r, (n + 4 : ℕ) - r), by ring⟩ ≫
          (chainModelDuality A i).b r - 𝟙 _ =
        chainModelH' A i r ≫ (dualCx (chainModel A i) ((n + 4 : ℕ) : ℤ)).d (r + 1) r +
          (dualCx (chainModel A i) ((n + 4 : ℕ) : ℤ)).d r (r - 1) ≫ chainModelH' A i (r - 1) ≫
            eqToHom (congrArg (dualCx (chainModel A i) ((n + 4 : ℕ) : ℤ)).X (by ring)) := by
  intro r
  have ex := chainModel_inverse_exact A i r
  have cm' : ∀ r s : ℤ, s = r - 1 → (chainModelDuality A i).b r ≫
      (dualCx (chainModel A i) ((n + 4 : ℕ) : ℤ)).d r s =
        (chainModel A i).d r s ≫ (chainModelDuality A i).b s := by
    intro r s h; subst h; exact chainModel_inverse_chainMap A i r
  have Ucm : chainModelStructureU A i ⟨(r, (n + 4 : ℕ) - r), by ring⟩ ≫
      (chainModel A i).d r (r - 1) = (dualCx (chainModel A i) ((n + 4 : ℕ) : ℤ)).d r (r - 1) ≫
        chainModelStructureU A i ⟨(r - 1, (n + 4 : ℕ) - (r - 1)), by ring⟩ :=
    (StructureCx.toHom (chainModelStructureU A i) (chainModelStructureU_cycle A i)).comm r (r - 1)
  have hN : r + (((n + 4 : ℕ) : ℤ) - r) = ((n + 4 : ℕ) : ℤ) := by ring
  have step1 : (chainModelDuality A i).φ ⟨(r, (n + 4 : ℕ) - r), hN⟩ ≫
      (chainModelDuality A i).b r - 𝟙 _ =
      chainModelStructureU A i ⟨(r, (n + 4 : ℕ) - r), hN⟩ ≫
        ((chainModelDuality A i).b r ≫ (chainModelDuality A i).φ ⟨(r, (n + 4 : ℕ) - r), hN⟩ -
          𝟙 _) ≫ (chainModelDuality A i).b r := by
    simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp, ← Category.assoc, ex.1]
  rw [step1, chainModel_homotopy A i r, Preadditive.add_comp, Preadditive.comp_add]
  simp (config := { proj := false }) only [Category.assoc]
  rw [← cm' (r + 1) r (by ring),
    ← Category.assoc (chainModelStructureU A i ⟨(r, (n + 4 : ℕ) - r), hN⟩)
      ((chainModel A i).d r (r - 1)), Ucm,
    famD_eqToHom (fun t => (chainModelDuality A i).b t) (show r - 1 + 1 = r by ring),
    chainModelH'_conj A i r, chainModelH'_conj A i (r - 1)]
  simp (config := { proj := false }) only [Category.assoc]

end HSP.ChainModels
