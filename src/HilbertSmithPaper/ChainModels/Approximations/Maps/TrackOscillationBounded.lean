import Mathlib
import HilbertSmithPaper.ChainModels.Approximations.Maps.TrackOscillation
import HilbertSmithPaper.ChainModels.Torus.DistLeTwo

/-!
# The track oscillation is bounded

The track oscillation is bounded above by `2`, the `d_∞`-diameter of the torus.

## Encoding

`trackOscillation_bddAbove A t` (the declaration of the article).
-/

namespace HSP.ChainModels

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The supremum in `ω(t)` is finite: the set is bounded above by `2`. -/
lemma trackOscillation_bddAbove (A : LocalDatum p n D ρplus) (t : ℝ) :
    BddAbove (trackOscillation A t) :=
  ⟨2, by rintro δ ⟨L, -, x, x', -, rfl⟩; exact Torus.dist_le_two _ _⟩

end HSP.ChainModels
