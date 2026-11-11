import Mathlib
import HilbertSmithPaper.LocalData.Control.ControlActionIsometric

/-!
# The control space is an isometric `C_p`-space

`C_p` acts by isometries of the metric space `(T, d_T)`.

## Encoding

`HSP.LocalDatum.instIsIsometricVAddT` (the declaration of the article) is the instance of
Mathlib's `IsIsometricVAdd (ZMod p) A.T`, from `d_T (c +ᵥ s) (c +ᵥ t) = d_T s t`.
-/

namespace HSP

/-- `C_p` acts by isometries of the metric space `(T, d_T)`. -/
instance LocalDatum.instIsIsometricVAddT {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}
    (A : LocalDatum p n D ρplus) : IsIsometricVAdd (ZMod p) A.T :=
  ⟨fun c => Isometry.of_dist_eq fun s t => A.dT_vadd c s t⟩

end HSP
