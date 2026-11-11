import Mathlib
import HilbertSmithPaper.ChainModels.Grid.ChainModelDuality
import HilbertSmithPaper.ChainModels.Grid.Poincare.ChainModelStructureU
import HilbertSmithPaper.ChainModels.Grid.Poincare.ChainModelInverseExact
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.UnitStructureCycle
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.StrProdLeibniz
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.StrProdZeroLeft
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.StrProdZeroRight
import HilbertSmithPaper.LTheory.Base.Complexes.CycleChainMap
import HilbertSmithPaper.LTheory.Base.Complexes.DualComplex

/-!
# The chain-model inverse is a chain map

`b_i` is a chain map `D_i → D_i^{N-*}`, where `d_r = (-1)^r d^*` on `D_i^{N-*}`.

## Proof

`φ_i^u` is a cycle (Leibniz rule, `∂φ = 0` on the circle, `∂φ_P = 0`), so `(φ_i^u)_♮` is a chain
map, and `b_i` is its exact inverse in every degree: `b d = b d φ^u b = b φ^u d b = d b`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.ChainModels

open FreeQ DualCat

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

private lemma gridStructureU_cycle (k : ℕ) :
    ∀ n : ℕ, (StructureCx (gridComplex k n)).d n (n - 1) (gridStructureU k n) = 0
  | 0 => unitStructure_cycle
  | n + 1 => by
    refine (basedStrProd_d (circleComplex_dim_neg k) (n : ℤ) 1 ((n +
        1 : ℕ) : ℤ) (by push_cast; ring)
      (gridStructureU k n) (circlePhi k)).trans ?_
    have hc : (StructureCx (circleComplex k)).d 1 (1 - 1) (circlePhi k) =
        0 := (circle_duality k).1.1
    rw [gridStructureU_cycle k n, hc, basedStrProd_zero_left, basedStrProd_zero_right, smul_zero,
      add_zero]
    rfl

private lemma structureU_cycle (A : LocalDatum p n D ρplus) (i : ℕ) :
    (StructureCx (chainModel A i)).d ((n + 4 : ℕ) : ℤ) ((n + 4 : ℕ) - 1)
      (chainModelStructureU A i) = 0 := by
  refine (basedStrProd_d cp2Complex_dim_neg (n : ℤ) 4 ((n + 4 : ℕ) : ℤ) (by push_cast; ring)
    (gridStructureU (meshSequence A i) n) cp2Structure).trans ?_
  have hc : (StructureCx cp2Complex).d 4 (4 - 1) cp2Structure = 0 := cp2Cells.cycle
  rw [gridStructureU_cycle, hc, basedStrProd_zero_left, basedStrProd_zero_right, smul_zero,
      add_zero]
  rfl

/-- *The chain-model inverse is a chain map*: `b_i` is a chain map `D_i → D_i^{N-*}`,
where `d_r = (-1)^r d^*` on `D_i^{N-*}`. -/
theorem chainModel_inverse_chainMap (A : LocalDatum p n D ρplus) (i : ℕ) :
    ∀ r : ℤ, (chainModelDuality A i).b r ≫ (dualCx (chainModel A i) ((n + 4 : ℕ) : ℤ)).d r
        (r - 1) = (chainModel A i).d r (r - 1) ≫ (chainModelDuality A i).b (r - 1) := by
  intro r
  have hc : chainModelStructureU A i ⟨(r, (n + 4 : ℕ) - r), by ring⟩ ≫
      (chainModel A i).d r (r - 1) =
      (dualCx (chainModel A i) ((n + 4 : ℕ) : ℤ)).d r (r - 1) ≫
        chainModelStructureU A i ⟨(r - 1, (n + 4 : ℕ) - (r - 1)), by ring⟩ :=
    (StructureCx.toHom (chainModelStructureU A i) (structureU_cycle A i)).comm r (r - 1)
  have e1 := chainModel_inverse_exact A i r
  have e2 := chainModel_inverse_exact A i (r - 1)
  rw [← Category.comp_id ((dualCx (chainModel A i) ((n + 4 : ℕ) : ℤ)).d r (r - 1)), ← e2.1,
    ← Category.assoc ((dualCx (chainModel A i) ((n + 4 : ℕ) : ℤ)).d r (r - 1)), ← hc,
    Category.assoc, ← Category.assoc ((chainModelDuality A i).b r), e1.2, Category.id_comp]

end HSP.ChainModels
