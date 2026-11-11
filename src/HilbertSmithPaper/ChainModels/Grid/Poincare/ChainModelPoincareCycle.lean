import Mathlib
import HilbertSmithPaper.ChainModels.Grid.ChainModelDuality
import HilbertSmithPaper.LTheory.Base.Complexes.StructureInvolution
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.StrProdLeibniz
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.StrProdInvolution
import HilbertSmithPaper.ChainModels.Grid.Tensor.KronZero
import HilbertSmithPaper.ChainModels.Grid.Cp2DimNeg
import HilbertSmithPaper.ChainModels.Grid.Cubical.CubicalTorusGrid
import HilbertSmithPaper.ChainModels.Grid.Cubical.UnitComplex
import HilbertSmithPaper.ChainModels.Grid.Cubical.CircleDimNeg
import HilbertSmithPaper.ChainModels.Grid.Cubical.CircleComplex

/-!
# The chain model is Poincaré: part 1

`∂φ_i = 0` and `Tφ_i = φ_i`.

## Proof

Induction over the circle factors with the Leibniz rule and the involution rule for products of structures, from circle
duality (2), the cells of `CP²` and the unit structure; a product with a zero factor vanishes.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.ChainModels

open FreeQ DualCat

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

private lemma basedStrProd_zero_left {C E : ChainComplex FreeQ ℤ} (hE : ∀ q < 0, (E.X q).dim = 0)
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

private lemma basedStrProd_zero_right {C E : ChainComplex FreeQ ℤ} (hE : ∀ q < 0, (E.X q).dim = 0)
    (m m' k : ℤ) (hk : m + m' = k) (φ : (StructureCx C).X m) :
    basedStrProd C E hE m m' k hk φ 0 = 0 := by
  funext x
  refine (Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_).trans rfl
  by_cases h' : ((b : ℕ) : ℤ) = m - (a : ℕ)
  · simp only [h', ↓reduceDIte]
    rw [show ((0 : (StructureCx E).X m') ⟨(x.1.1 - (a : ℕ), m' - (x.1.1 - (a : ℕ))), by ring⟩) = 0
        from rfl, basedKron_eq_zero (Or.inr rfl)]
    simp only [zero_comp, comp_zero, smul_zero]
    rfl
  · simp only [h', ↓reduceDIte]

private lemma unitComplex_d (i j : ℤ) : unitComplex.d i j = 0 := by
  show ChainComplex.of.d (fun r => (⟨unitDim r⟩ : FreeQ)) (fun _ => 0) i j = 0
  unfold ChainComplex.of.d
  split_ifs <;> simp

private lemma unitStructure_cycle : (StructureCx unitComplex).d 0 (0 - 1) unitStructure = 0 := by
  funext ⟨⟨a, b⟩, h⟩
  rw [StructureCx.d_apply unitComplex 0 (0 - 1) unitStructure a b h (0 - b) (0 - a) (by omega)
    (by omega)]
  simp only [unitComplex_d, comp_zero, dualHom_zero, zero_comp, smul_zero, add_zero]
  rfl

private lemma eq_zero_of_unitDim_ne {r : ℤ} (h : unitDim r ≠ 0) : r = 0 := by
  rcases r with (_ | r) | r
  · rfl
  · exact absurd rfl h
  · exact absurd rfl h

private lemma unitStructure_symmetric :
    (StructureCx.T unitComplex).f 0 unitStructure = unitStructure := by
  funext ⟨⟨a, b⟩, h⟩
  rw [StructureCx.T_apply]
  refine Matrix.ext fun x y => ?_
  have ha : a = 0 := eq_zero_of_unitDim_ne fun e => (Fin.cast e x).elim0
  subst ha
  rw [zero_mul, Int.negOnePow_zero, one_smul, eqToHom_refl, Category.comp_id]
  rfl

private lemma gridStructure_cycle (k : ℕ) :
    ∀ n : ℕ, (StructureCx (gridComplex k n)).d n (n - 1) (gridStructure k n) = 0
  | 0 => unitStructure_cycle
  | n + 1 => by
    refine (basedStrProd_d (circleComplex_dim_neg k) (n : ℤ) 1 ((n + 1 : ℕ) : ℤ) (by push_cast; ring)
      (gridStructure k n) (circlePhiSym k)).trans ?_
    have hc : (StructureCx (circleComplex k)).d 1 (1 - 1) (circlePhiSym k) = 0 :=
      (circle_duality k).2.1.2.2.1
    rw [gridStructure_cycle k n, hc, basedStrProd_zero_left, basedStrProd_zero_right, smul_zero,
      add_zero]
    rfl

private lemma gridStructure_symmetric (k : ℕ) :
    ∀ n : ℕ, (StructureCx.T (gridComplex k n)).f n (gridStructure k n) = gridStructure k n
  | 0 => unitStructure_symmetric
  | n + 1 => by
    refine (basedStrProd_T (circleComplex_dim_neg k) (n : ℤ) 1 ((n + 1 : ℕ) : ℤ) (by push_cast; ring)
      (gridStructure k n) (circlePhiSym k)).trans ?_
    rw [gridStructure_symmetric k n, (circle_duality k).2.1.2.2.2]
    rfl

/-- *The chain model is Poincaré*, part 1: `∂φ_i = 0` and `Tφ_i = φ_i`. -/
theorem chainModel_poincare_cycle (A : LocalDatum p n D ρplus) (i : ℕ) :
    ((StructureCx (chainModel A i)).d ((n + 4 : ℕ) : ℤ) ((n + 4 : ℕ) - 1)
        (chainModelDuality A i).φ = 0 ∧
      (StructureCx.T (chainModel A i)).f ((n + 4 : ℕ) : ℤ) (chainModelDuality A i).φ =
        (chainModelDuality A i).φ) := by
  constructor
  · refine (basedStrProd_d cp2Complex_dim_neg (n : ℤ) 4 ((n + 4 : ℕ) : ℤ) (by push_cast; ring)
      (gridStructure (meshSequence A i) n) cp2Structure).trans ?_
    have hc : (StructureCx cp2Complex).d 4 (4 - 1) cp2Structure = 0 := cp2Cells.cycle
    rw [gridStructure_cycle, hc, basedStrProd_zero_left, basedStrProd_zero_right, smul_zero,
      add_zero]
    rfl
  · refine (basedStrProd_T cp2Complex_dim_neg (n : ℤ) 4 ((n + 4 : ℕ) : ℤ) (by push_cast; ring)
      (gridStructure (meshSequence A i) n) cp2Structure).trans ?_
    have hs : (StructureCx.T cp2Complex).f 4 cp2Structure = cp2Structure := cp2Cells.symmetric
    rw [gridStructure_symmetric, hs]
    rfl

end HSP.ChainModels
