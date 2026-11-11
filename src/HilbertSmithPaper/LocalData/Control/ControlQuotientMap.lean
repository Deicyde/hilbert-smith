import Mathlib
import HilbertSmithPaper.LocalData.Control.ControlSpace

/-!
# The quotient map to the control space

The quotient map `π : Z⁺ → T` sends a point to its `H₁`-orbit.

## Encoding

`HSP.LocalDatum.π` (the declaration of the article) is `Quotient.mk`.
-/

namespace HSP

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The quotient map `π : Z⁺ → T`. -/
noncomputable def LocalDatum.π (A : LocalDatum p n D ρplus) : A.Zplus → A.T :=
  Quotient.mk _

end HSP
