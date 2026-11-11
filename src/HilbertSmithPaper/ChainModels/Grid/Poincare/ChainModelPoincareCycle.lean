import Mathlib
import HilbertSmithPaper.ChainModels.Grid.ChainModelDuality
import HilbertSmithPaper.LTheory.Base.Complexes.StructureInvolution
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.StrProdLeibniz
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.StrProdInvolution
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.StrProdZeroLeft
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.StrProdZeroRight
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.UnitStructureCycle
import HilbertSmithPaper.ChainModels.Grid.Cp2.Cp2DimNeg
import HilbertSmithPaper.ChainModels.Grid.Cubical.CubicalTorusGrid
import HilbertSmithPaper.ChainModels.Grid.Cubical.UnitComplex
import HilbertSmithPaper.ChainModels.Grid.Cubical.CircleDimNeg
import HilbertSmithPaper.ChainModels.Grid.Cubical.CircleComplex
import HilbertSmithPaper.ChainModels.Grid.Cp2.Cp2Cells
import HilbertSmithPaper.ChainModels.Grid.Cp2.Cp2Structure
import HilbertSmithPaper.ChainModels.Grid.Cp2.Cp2Complex
import HilbertSmithPaper.ChainModels.Grid.Model.GridStructure
import HilbertSmithPaper.ChainModels.Grid.Model.UnitStructure

/-!
# The chain model is Poincaré: part 1

`∂φ_i = 0` and `Tφ_i = φ_i`.

## Proof

Induction over the circle factors with the Leibniz rule and the involution rule for products of
structures, from circle duality (2), the cells of `CP²` and the unit structure; a product with a
zero factor vanishes.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.ChainModels

open FreeQ DualCat

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

private lemma eq_zero_of_unit_dim_ne {r : ℤ} (h : (unitComplex.X r).dim ≠ 0) : r = 0 := by
  by_contra hr
  exact h (unitComplex_X_dim_of_ne hr)

private lemma unitStructure_symmetric :
    (StructureCx.T unitComplex).f 0 unitStructure = unitStructure := by
  funext ⟨⟨a, b⟩, h⟩
  rw [StructureCx.T_apply]
  refine Matrix.ext fun x y => ?_
  have ha : a = 0 := eq_zero_of_unit_dim_ne fun e => (Fin.cast e x).elim0
  subst ha
  rw [zero_mul, Int.negOnePow_zero, one_smul, eqToHom_refl, Category.comp_id]
  rfl

private lemma gridStructure_cycle (k : ℕ) :
    ∀ n : ℕ, (StructureCx (gridComplex k n)).d n (n - 1) (gridStructure k n) = 0
  | 0 => unitStructure_cycle
  | n + 1 => by
    refine (basedStrProd_d (circleComplex_dim_neg k) (n : ℤ) 1 ((n +
        1 : ℕ) : ℤ) (by push_cast; ring)
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
    refine (basedStrProd_T (circleComplex_dim_neg k) (n : ℤ) 1 ((n +
        1 : ℕ) : ℤ) (by push_cast; ring)
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
