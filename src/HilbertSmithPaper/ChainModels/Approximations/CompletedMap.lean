import Mathlib
import HilbertSmithPaper.ChainModels.Torus.Proj
import HilbertSmithPaper.ChainModels.Torus.Lift
import HilbertSmithPaper.LocalData.Chart.LocalDatum
import HilbertSmithPaper.ChainModels.Approximations.Maps.CompletedMapEuclid
import HilbertSmithPaper.ChainModels.Grid.Torus

/-!
# Completed map

For a local datum and `a ∈ ℤ_p`, the completed map `â` interpolates between the action of `a`
on `B(0,1)` and the identity off `B(0,3/2)`, through the cutoff
`θ(x) = min(1, max(0, 3 - 2|x|))`: `â(x) = x + θ(x)(a·x - x)` for `|x| < 2`, and `â(x) = x`
otherwise. Being the identity near the boundary of `[-2,2]ⁿ`, it induces the self-map
`x ↦ q(â(x̃))` of the torus.

## Encoding

* `ℝⁿ` is `EuclideanSpace ℝ (Fin n)`. The point `a·x` is the action of the local datum on the
  subtype `Ω`, applied to `x` viewed in `Ω` through `B(0,2) ⊆ Ω`.
* `completedMapEuclid` is `â` on `ℝⁿ`; `completedMap` (the declaration of the article) is the
  induced map `q ∘ â ∘ lift` of `𝕋ⁿ`, with the lift to `[-2,2)ⁿ` and the quotient `q` of the
  torus article.
-/

namespace HSP.ChainModels

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The completed map `â` of the torus `𝕋ⁿ`: `x ↦ q(â(x̃))`, with `x̃ ∈ [-2,2)ⁿ` the lift. -/
noncomputable def completedMap (A : LocalDatum p n D ρplus) (a : ℤ_[p]) (x : Torus n) :
    Torus n :=
  Torus.proj (completedMapEuclid A a (Torus.lift x))

end HSP.ChainModels
