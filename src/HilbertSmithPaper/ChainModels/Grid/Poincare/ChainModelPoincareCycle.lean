import Mathlib
import HilbertSmithPaper.ChainModels.Grid.ChainModelDuality
import HilbertSmithPaper.LTheory.Base.Complexes.StructureInvolution

/-!
# The chain model is Poincaré: part 1

`∂φ_i = 0` and `Tφ_i = φ_i`.
-/

open CategoryTheory

namespace HSP.ChainModels

open FreeQ DualCat

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- *The chain model is Poincaré*, part 1: `∂φ_i = 0` and `Tφ_i = φ_i`. -/
theorem chainModel_poincare_cycle (A : LocalDatum p n D ρplus) (i : ℕ) :
    ((StructureCx (chainModel A i)).d ((n + 4 : ℕ) : ℤ) ((n + 4 : ℕ) - 1)
        (chainModelDuality A i).φ = 0 ∧
      (StructureCx.T (chainModel A i)).f ((n + 4 : ℕ) : ℤ) (chainModelDuality A i).φ =
        (chainModelDuality A i).φ) := by
  sorry

end HSP.ChainModels
