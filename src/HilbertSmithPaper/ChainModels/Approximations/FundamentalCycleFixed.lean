import Mathlib
import HilbertSmithPaper.ChainModels.Approximations.GroupApprox
import HilbertSmithPaper.ChainModels.Grid.Model.ChainModelFundamental

/-!
# Approximations fix the fundamental cycle

Every `N`-cycle of `D_i` is a rational multiple of `z_i`, and `a_g z_i = z_i` for `g ∈ G_i`.

## Encoding

Chains of `(D_i)_N`, `N = n + 4`, are columns `⟨1⟩ ⟶ (D_i)_N`; `z_i` is
`chainModelFundamental`, and `a_g z_i` is `z_i ≫ (a_g)_N`.
-/

open CategoryTheory

namespace HSP.ChainModels

open FreeQ

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- **Approximations fix the fundamental cycle.** Every `N`-cycle of `D_i` is a rational multiple
of `z_i`, and `a_g z_i = z_i` for every `g ∈ G_i`. -/
theorem approx_fundamentalCycle (A : LocalDatum p n D ρplus) (i : ℕ) :
    (∀ z : (⟨1⟩ : FreeQ) ⟶ (chainModel A i).X ((n + 4 : ℕ) : ℤ),
      z ≫ (chainModel A i).d ((n + 4 : ℕ) : ℤ) ((n + 4 : ℕ) - 1) = 0 →
        ∃ q : ℚ, z = q • chainModelFundamental A i) ∧
    ∀ g : ZMod (p ^ i),
      chainModelFundamental A i ≫ groupApprox A i g ((n + 4 : ℕ) : ℤ) = chainModelFundamental A i := by
  sorry

end HSP.ChainModels
