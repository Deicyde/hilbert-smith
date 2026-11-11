import Mathlib
import HilbertSmithPaper.ChainModels.Grid.ChainModelDuality
import HilbertSmithPaper.ChainModels.Grid.Poincare.ChainModelStructureU
import HilbertSmithPaper.ChainModels.Grid.Cp2.Cp2Cells
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.UnitStructureCycle
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.StrProdLeibniz
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.StrProdZeroLeft
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.StrProdZeroRight

/-!
# The unsymmetrized structure of the chain model is a cycle

`∂φ_i^u = 0`.

## Proof

Induction over the circle factors with the Leibniz rule, from the unit structure, `∂φ = 0` on
the circle (circle duality (1)) and `∂φ_P = 0`; a product with a zero factor vanishes.
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

/-- *The unsymmetrized structure of the chain model is a cycle*: `∂φ_i^u = 0`. -/
lemma chainModelStructureU_cycle (A : LocalDatum p n D ρplus) (i : ℕ) :
    (StructureCx (chainModel A i)).d ((n + 4 : ℕ) : ℤ) ((n + 4 : ℕ) - 1)
      (chainModelStructureU A i) = 0 := by
  refine (basedStrProd_d cp2Complex_dim_neg (n : ℤ) 4 ((n + 4 : ℕ) : ℤ) (by push_cast; ring)
    (gridStructureU (meshSequence A i) n) cp2Structure).trans ?_
  have hc : (StructureCx cp2Complex).d 4 (4 - 1) cp2Structure = 0 := cp2Cells.cycle
  rw [gridStructureU_cycle, hc, basedStrProd_zero_left, basedStrProd_zero_right, smul_zero,
      add_zero]
  rfl

end HSP.ChainModels
