import Mathlib
import HilbertSmithPaper.ChainModels.Grid.ChainModelDuality
import HilbertSmithPaper.ChainModels.Grid.Poincare.ChainModelH
import HilbertSmithPaper.ChainModels.Grid.Poincare.ChainModelHDual
import HilbertSmithPaper.Categories.Asymptotic.Propagation

/-!
# The chain model is Poincaré: part 3

With cells and duals labelled at their centers, `φ_i`, `b_i`, `H_i`, `H'_i` have `d_∞`-propagation at most `h_i = 4/k_i`.
-/

open CategoryTheory

namespace HSP.ChainModels

open FreeQ DualCat

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- *The chain model is Poincaré*, part 3: With cells and duals labelled at their centers, `φ_i`, `b_i`, `H_i`, `H'_i` have `d_∞`-propagation at most `h_i = 4/k_i`. -/
theorem chainModel_poincare_propagation (A : LocalDatum p n D ρplus) (i : ℕ) :
    ((∀ x, (prop (chainModelLabel A i x.1.2) (chainModelLabel A i x.1.1)
          ((chainModelDuality A i).φ x) : ℝ) ≤ 4 / meshSequence A i) ∧
      (∀ r, (prop (chainModelLabel A i r) (chainModelLabel A i ((n + 4 : ℕ) - r))
          ((chainModelDuality A i).b r) : ℝ) ≤ 4 / meshSequence A i) ∧
      (∀ r, (prop (chainModelLabel A i r) (chainModelLabel A i (r + 1)) (chainModelH A i r) : ℝ) ≤
        4 / meshSequence A i) ∧
      (∀ r, (prop (chainModelLabel A i ((n + 4 : ℕ) - r))
          (chainModelLabel A i ((n + 4 : ℕ) - (r + 1))) (chainModelH' A i r) : ℝ) ≤
        4 / meshSequence A i)) := by
  sorry

end HSP.ChainModels
