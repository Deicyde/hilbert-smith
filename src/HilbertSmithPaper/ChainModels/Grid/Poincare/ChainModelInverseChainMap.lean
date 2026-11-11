import Mathlib
import HilbertSmithPaper.ChainModels.Grid.ChainModelDuality
import HilbertSmithPaper.LTheory.Base.Complexes.DualComplex

/-!
# The chain-model inverse is a chain map

`b_i` is a chain map `D_i → D_i^{N-*}`, where `d_r = (-1)^r d^*` on `D_i^{N-*}`.
-/

open CategoryTheory

namespace HSP.ChainModels

open FreeQ DualCat

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- *The chain-model inverse is a chain map*: `b_i` is a chain map `D_i → D_i^{N-*}`, where `d_r = (-1)^r d^*` on `D_i^{N-*}`. -/
theorem chainModel_inverse_chainMap (A : LocalDatum p n D ρplus) (i : ℕ) :
    ∀ r : ℤ, (chainModelDuality A i).b r ≫ (dualCx (chainModel A i) ((n + 4 : ℕ) : ℤ)).d r
        (r - 1) = (chainModel A i).d r (r - 1) ≫ (chainModelDuality A i).b (r - 1) := by
  sorry

end HSP.ChainModels
