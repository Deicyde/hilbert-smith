import Mathlib
import HilbertSmithPaper.ChainModels.Grid.ChainModelDuality
import HilbertSmithPaper.ChainModels.Grid.Poincare.ChainModelH
import HilbertSmithPaper.LTheory.Base.Complexes.DualComplex

/-!
# The chain-model homotopy

`φ_i b_i - 1 = dH_i + H_i d` on `D_i`.
-/

open CategoryTheory

namespace HSP.ChainModels

open FreeQ DualCat

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- *The chain-model homotopy*: `φ_i b_i - 1 = dH_i + H_i d` on `D_i`. -/
theorem chainModel_homotopy (A : LocalDatum p n D ρplus) (i : ℕ) :
    ∀ r : ℤ, (chainModelDuality A i).b r ≫
          (chainModelDuality A i).φ ⟨(r, (n + 4 : ℕ) - r), by ring⟩ - 𝟙 _ =
        chainModelH A i r ≫ (chainModel A i).d (r + 1) r +
          (chainModel A i).d r (r - 1) ≫ chainModelH A i (r - 1) ≫
            eqToHom (congrArg (chainModel A i).X (by ring)) := by
  sorry

end HSP.ChainModels
