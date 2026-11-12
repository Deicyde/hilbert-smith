import Mathlib
import HilbertSmithPaper.ChainModels.Grid.ChainModelDuality
import HilbertSmithPaper.ChainModels.Grid.Poincare.ChainModelStructureU
import HilbertSmithPaper.ChainModels.Grid.Poincare.ChainModelStructureUCycle
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
    (StructureCx.toHom (chainModelStructureU A i) (chainModelStructureU_cycle A i)).comm r (r - 1)
  have e1 := chainModel_inverse_exact A i r
  have e2 := chainModel_inverse_exact A i (r - 1)
  rw [← Category.comp_id ((dualCx (chainModel A i) ((n + 4 : ℕ) : ℤ)).d r (r - 1)), ← e2.1,
    ← Category.assoc ((dualCx (chainModel A i) ((n + 4 : ℕ) : ℤ)).d r (r - 1)), ← hc,
    Category.assoc, ← Category.assoc ((chainModelDuality A i).b r), e1.2, Category.id_comp]

end HSP.ChainModels
