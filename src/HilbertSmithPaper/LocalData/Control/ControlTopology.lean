import Mathlib
import HilbertSmithPaper.LocalData.Control.ControlSpace

/-!
# The quotient topology on the control space

The control space `T = Z⁺ / H₁` carries the quotient topology of `Z⁺`.

## Encoding

`HSP.LocalDatum.instTopologicalSpaceT` (the declaration of the article) is the instance of
Mathlib's quotient topology on `Quotient (AddAction.orbitRel (padicSubgroup p 1) A.Zplus)`.
-/

namespace HSP

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The quotient topology on the control space. -/
instance LocalDatum.instTopologicalSpaceT (A : LocalDatum p n D ρplus) :
    TopologicalSpace A.T :=
  inferInstanceAs (TopologicalSpace (Quotient (AddAction.orbitRel (padicSubgroup p 1) A.Zplus)))

end HSP
