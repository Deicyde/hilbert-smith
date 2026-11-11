import Mathlib
import HilbertSmithPaper.ChainModels.Approximations.Maps.CompletedMapEuclid

/-!
# The track map on Euclidean space

For `a, b, c ∈ ℤ_p` and `t ∈ [0,1]`, the track map `L_{a,b,c,t} = (1-t) â b̂ + t ĉ` on `ℝⁿ`.

## Encoding

`trackMapEuclid A a b c t` (the declaration of the article); `t` ranges over `unitInterval`.
-/

namespace HSP.ChainModels

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The track map `L_{a,b,c,t} = (1-t) â b̂ + t ĉ` on `ℝⁿ`. -/
noncomputable def trackMapEuclid (A : LocalDatum p n D ρplus) (a b c : ℤ_[p]) (t : unitInterval)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  (1 - (t : ℝ)) • completedMapEuclid A a (completedMapEuclid A b x) +
    (t : ℝ) • completedMapEuclid A c x

end HSP.ChainModels
