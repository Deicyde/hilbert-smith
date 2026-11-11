import Mathlib
import HilbertSmithPaper.ChainModels.Approximations.TrackMap

/-!
# The track family

The family `𝓕` of all track maps `L_{a,b,c,t}` of the torus, `a, b, c ∈ ℤ_p`, `t ∈ [0,1]`.

## Encoding

`trackFamily A` (the declaration of the article) is the range of `trackMap A`.
-/

namespace HSP.ChainModels

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The family `𝓕` of all track maps of the torus. -/
def trackFamily (A : LocalDatum p n D ρplus) : Set (Torus n → Torus n) :=
  Set.range fun q : ℤ_[p] × ℤ_[p] × ℤ_[p] × unitInterval => trackMap A q.1 q.2.1 q.2.2.1 q.2.2.2

end HSP.ChainModels
