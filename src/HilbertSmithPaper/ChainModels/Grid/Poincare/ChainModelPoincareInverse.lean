import Mathlib
import HilbertSmithPaper.ChainModels.Grid.ChainModelDuality
import HilbertSmithPaper.ChainModels.Grid.Poincare.ChainModelStructureU
import HilbertSmithPaper.ChainModels.Grid.Poincare.ChainModelH
import HilbertSmithPaper.ChainModels.Grid.Poincare.ChainModelHDual
import HilbertSmithPaper.LTheory.Base.Complexes.DualComplex

/-!
# The chain model is Poincaré: part 2

`b_i` is a chain map and the exact inverse of `(φ_i^u)_♮`; `φ_i b_i - 1 = dH_i + H_i d` and `b_i φ_i - 1 = dH'_i + H'_i d`.
-/

open CategoryTheory

namespace HSP.ChainModels

open FreeQ DualCat

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- *The chain model is Poincaré*, part 2: `b_i` is a chain map and the exact inverse of `(φ_i^u)_♮`; `φ_i b_i - 1 = dH_i + H_i d` and `b_i φ_i - 1 = dH'_i + H'_i d`. -/
theorem chainModel_poincare_inverse (A : LocalDatum p n D ρplus) (i : ℕ) :
    ((∀ r : ℤ, (chainModelDuality A i).b r ≫ (dualCx (chainModel A i) ((n + 4 : ℕ) : ℤ)).d r
        (r - 1) = (chainModel A i).d r (r - 1) ≫ (chainModelDuality A i).b (r - 1)) ∧
      (∀ r : ℤ, chainModelStructureU A i ⟨(r, (n + 4 : ℕ) - r), by ring⟩ ≫
          (chainModelDuality A i).b r = 𝟙 _ ∧
        (chainModelDuality A i).b r ≫ chainModelStructureU A i ⟨(r, (n + 4 : ℕ) - r), by ring⟩ =
          𝟙 _) ∧
      (∀ r : ℤ, (chainModelDuality A i).b r ≫
          (chainModelDuality A i).φ ⟨(r, (n + 4 : ℕ) - r), by ring⟩ - 𝟙 _ =
        chainModelH A i r ≫ (chainModel A i).d (r + 1) r +
          (chainModel A i).d r (r - 1) ≫ chainModelH A i (r - 1) ≫
            eqToHom (congrArg (chainModel A i).X (by ring))) ∧
      (∀ r : ℤ, (chainModelDuality A i).φ ⟨(r, (n + 4 : ℕ) - r), by ring⟩ ≫
          (chainModelDuality A i).b r - 𝟙 _ =
        chainModelH' A i r ≫ (dualCx (chainModel A i) ((n + 4 : ℕ) : ℤ)).d (r + 1) r +
          (dualCx (chainModel A i) ((n + 4 : ℕ) : ℤ)).d r (r - 1) ≫ chainModelH' A i (r - 1) ≫
            eqToHom (congrArg (dualCx (chainModel A i) ((n + 4 : ℕ) : ℤ)).X (by ring)))) := by
  sorry

end HSP.ChainModels
