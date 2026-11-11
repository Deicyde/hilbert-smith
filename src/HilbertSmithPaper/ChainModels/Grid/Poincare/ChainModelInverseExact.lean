import Mathlib
import HilbertSmithPaper.ChainModels.Grid.ChainModelDuality
import HilbertSmithPaper.ChainModels.Grid.Poincare.ChainModelStructureU
import HilbertSmithPaper.LTheory.Base.Complexes.DualComplex

/-!
# The chain-model inverse is exact

`b_i` is the exact inverse of `(φ_i^u)_♮`: `φ_i^u b_i = 1` and `b_i φ_i^u = 1` in every degree.
-/

open CategoryTheory

namespace HSP.ChainModels

open FreeQ DualCat

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- *The chain-model inverse is exact*: `b_i` is the exact inverse of `(φ_i^u)_♮`: `φ_i^u b_i = 1` and `b_i φ_i^u = 1` in every degree. -/
theorem chainModel_inverse_exact (A : LocalDatum p n D ρplus) (i : ℕ) :
    ∀ r : ℤ, chainModelStructureU A i ⟨(r, (n + 4 : ℕ) - r), by ring⟩ ≫
          (chainModelDuality A i).b r = 𝟙 _ ∧
        (chainModelDuality A i).b r ≫ chainModelStructureU A i ⟨(r, (n + 4 : ℕ) - r), by ring⟩ =
          𝟙 _ := by
  sorry

end HSP.ChainModels
