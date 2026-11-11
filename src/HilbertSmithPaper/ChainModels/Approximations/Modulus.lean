import Mathlib
import HilbertSmithPaper.ChainModels.Approximations.TrackMap
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

/-- The set `{d_∞(Lx, Lx') : L ∈ 𝓕, d_∞(x, x') ≤ t}` whose supremum enters `ω(t)`. -/
def trackOscillation (A : LocalDatum p n D ρplus) (t : ℝ) : Set ℝ :=
  {δ | ∃ L ∈ trackFamily A, ∃ x x' : Torus n, dist x x' ≤ t ∧ δ = dist (L x) (L x')}

/-- The *modulus* `ω(t) = t + sup {d_∞(Lx, Lx') : L ∈ 𝓕, d_∞(x, x') ≤ t}` of the track family. -/
noncomputable def trackModulus (A : LocalDatum p n D ρplus) (t : ℝ) : ℝ :=
  t + sSup (trackOscillation A t)

/-- The supremum in `ω(t)` is finite: the set is bounded above by `2`. -/
lemma trackOscillation_bddAbove (A : LocalDatum p n D ρplus) (t : ℝ) :
    BddAbove (trackOscillation A t) :=
  ⟨2, by rintro δ ⟨L, -, x, x', -, rfl⟩; exact Torus.dist_le_two _ _⟩

end HSP.ChainModels
