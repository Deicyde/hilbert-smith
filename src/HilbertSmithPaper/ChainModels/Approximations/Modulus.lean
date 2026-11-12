import Mathlib
import HilbertSmithPaper.ChainModels.Torus.DistLeTwo
import HilbertSmithPaper.ChainModels.Approximations.Maps.TrackOscillation
import HilbertSmithPaper.ChainModels.Grid.Torus

/-!
# Modulus of the track family

`ω(t) = t + sup {d_∞(Lx, Lx') : L ∈ 𝓕, x, x' ∈ 𝕋ⁿ, d_∞(x, x') ≤ t}`, with `𝓕` the family of
track maps. The set is bounded above by `2`, the `d_∞`-diameter of the torus, so the supremum
is finite.

## Encoding

`d_∞` is `dist` on `Torus n`, and the supremum is `sSup` on `ℝ`. For `t < 0` the set is empty
and Mathlib's `sSup ∅ = 0`; the paper uses `t ≥ 0` only.
-/

namespace HSP.ChainModels

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The *modulus* `ω(t) = t + sup {d_∞(Lx, Lx') : L ∈ 𝓕, d_∞(x, x') ≤ t}` of the track family. -/
noncomputable def trackModulus (A : LocalDatum p n D ρplus) (t : ℝ) : ℝ :=
  t + sSup (trackOscillation A t)

end HSP.ChainModels
