import Mathlib
import HilbertSmithPaper.ChainModels.Grid.ChainModelDuality
import HilbertSmithPaper.ChainModels.Grid.Poincare.ChainModelHDual
import HilbertSmithPaper.LTheory.Base.Complexes.DualComplex

/-!
# The chain-model dual homotopy

`b_i φ_i - 1 = dH'_i + H'_i d` on `D_i^{N-*}`, where `d_r = (-1)^r d^*`.
-/

open CategoryTheory

namespace HSP.ChainModels

open FreeQ DualCat

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- *The chain-model dual homotopy*: `b_i φ_i - 1 = dH'_i + H'_i d` on `D_i^{N-*}`, where `d_r = (-1)^r d^*`. -/
theorem chainModel_dual_homotopy (A : LocalDatum p n D ρplus) (i : ℕ) :
    ∀ r : ℤ, (chainModelDuality A i).φ ⟨(r, (n + 4 : ℕ) - r), by ring⟩ ≫
          (chainModelDuality A i).b r - 𝟙 _ =
        chainModelH' A i r ≫ (dualCx (chainModel A i) ((n + 4 : ℕ) : ℤ)).d (r + 1) r +
          (dualCx (chainModel A i) ((n + 4 : ℕ) : ℤ)).d r (r - 1) ≫ chainModelH' A i (r - 1) ≫
            eqToHom (congrArg (dualCx (chainModel A i) ((n + 4 : ℕ) : ℤ)).X (by ring)) := by
  sorry

end HSP.ChainModels
