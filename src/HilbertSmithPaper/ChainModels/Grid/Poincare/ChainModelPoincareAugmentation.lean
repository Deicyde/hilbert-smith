import Mathlib
import HilbertSmithPaper.ChainModels.Grid.ChainModelDuality
import HilbertSmithPaper.ChainModels.Grid.Poincare.ChainModelAug

/-!
# The chain model is Poincaré: part 4

`ε φ_i(α) = α(z_i)` for every `α ∈ D_N^*`.
-/

open CategoryTheory

namespace HSP.ChainModels

open FreeQ DualCat

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- *The chain model is Poincaré*, part 4: `ε φ_i(α) = α(z_i)` for every `α ∈ D_N^*`. -/
theorem chainModel_poincare_augmentation (A : LocalDatum p n D ρplus) (i : ℕ) :
    ((chainModelDuality A i).φ ⟨(0, (n + 4 : ℕ)), by ring⟩ ≫ chainModelAug A i =
      dualHom (chainModelFundamental A i)) := by
  sorry

end HSP.ChainModels
