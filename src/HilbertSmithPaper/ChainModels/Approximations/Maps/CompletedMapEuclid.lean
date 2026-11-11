import Mathlib
import HilbertSmithPaper.ChainModels.Approximations.Maps.CompletedCutoff
import HilbertSmithPaper.LocalData.Chart.LocalDatum

/-!
# The completed map on Euclidean space

For a local datum and `a ∈ ℤ_p`, `â(x) = x + θ(x)(a·x - x)` for `|x| < 2`, and `â(x) = x`
otherwise, with `θ` the completed cutoff.

## Encoding

`completedMapEuclid A a` (the declaration of the article); `a·x` is the action of the local datum
on the subtype `Ω`, applied to `x` viewed in `Ω` through `B(0,2) ⊆ Ω`.
-/

namespace HSP.ChainModels

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The completed map `â` on `ℝⁿ`: `x + θ(x)(a·x - x)` for `|x| < 2`, and `x` otherwise. -/
noncomputable def completedMapEuclid (A : LocalDatum p n D ρplus) (a : ℤ_[p])
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  if h : ‖x‖ < 2 then
    x + completedCutoff x •
      (((a +ᵥ (⟨x, A.ball_subset (mem_ball_zero_iff.2 h)⟩ : A.Ω) : A.Ω) :
        EuclideanSpace ℝ (Fin n)) - x)
  else x

end HSP.ChainModels
