import Mathlib
import HilbertSmithPaper.ChainModels.Approximations.Maps.TrackFamily

/-!
# Track oscillation

For `t ∈ ℝ`, the set `{d_∞(Lx, Lx') : L ∈ 𝓕, x, x' ∈ 𝕋ⁿ, d_∞(x, x') ≤ t}` whose supremum
enters the modulus of the track family.

## Encoding

`trackOscillation A t` (the declaration of the article); `d_∞` is `dist` on `Torus n`.
-/

namespace HSP.ChainModels

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The set `{d_∞(Lx, Lx') : L ∈ 𝓕, d_∞(x, x') ≤ t}` whose supremum enters `ω(t)`. -/
def trackOscillation (A : LocalDatum p n D ρplus) (t : ℝ) : Set ℝ :=
  {δ | ∃ L ∈ trackFamily A, ∃ x x' : Torus n, dist x x' ≤ t ∧ δ = dist (L x) (L x')}

end HSP.ChainModels
