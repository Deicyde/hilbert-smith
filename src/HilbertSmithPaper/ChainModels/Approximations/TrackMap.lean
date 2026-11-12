import Mathlib
import HilbertSmithPaper.ChainModels.Torus.Proj
import HilbertSmithPaper.ChainModels.Torus.ProjLift
import HilbertSmithPaper.ChainModels.Torus.Lift
import HilbertSmithPaper.ChainModels.Approximations.Maps.TrackMapEuclid
import HilbertSmithPaper.ChainModels.Grid.Torus

/-!
# Track maps

For `a, b, c ∈ ℤ_p` and `t ∈ [0,1]`, the track map `L_{a,b,c,t} = (1-t) â b̂ + t ĉ` on `ℝⁿ`. It is
the identity off `B(0,3/2)`, so it induces the map `x ↦ q(L(x̃))` of the torus. The family `𝓕`
consists of all these torus maps; it contains every completed map `â = L_{a,0,a,t}` and the
identity `L_{0,0,0,t}`.

## Encoding

`trackMap` (the declaration of the article) is the map of `𝕋ⁿ` induced by `trackMapEuclid`;
`t` ranges over `unitInterval`.
-/

namespace HSP.ChainModels

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The track map `L_{a,b,c,t}` of the torus: `x ↦ q(L_{a,b,c,t}(x̃))`. -/
noncomputable def trackMap (A : LocalDatum p n D ρplus) (a b c : ℤ_[p]) (t : unitInterval)
    (x : Torus n) : Torus n :=
  Torus.proj (trackMapEuclid A a b c t (Torus.lift x))

end HSP.ChainModels
