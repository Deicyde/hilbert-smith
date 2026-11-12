import Mathlib
import HilbertSmithPaper.LocalData.Control.ZplusAction
import HilbertSmithPaper.LocalData.Subgroups.PadicSubgroups

/-!
# The control space

For a local datum, the control space is `T = Z⁺ / H₁`, the type of orbits of `H₁ = p ℤ_p` acting
on `Z⁺` by the restricted action, with the quotient topology and quotient map `π : Z⁺ → T`.

## Encoding

`T` is a `def` for Mathlib's `AddAction.orbitRel.Quotient (padicSubgroup p 1) A.Zplus`. Its
quotient topology (`HSP.LocalDatum.instTopologicalSpaceT`) and the quotient map
(`HSP.LocalDatum.π`) have their own modules.
-/

namespace HSP

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The control space `T = Z⁺ / H₁` of a local datum: the `H₁`-orbits of the restricted action on
`Z⁺`. -/
def LocalDatum.T (A : LocalDatum p n D ρplus) : Type :=
  AddAction.orbitRel.Quotient (padicSubgroup p 1) A.Zplus

end HSP
