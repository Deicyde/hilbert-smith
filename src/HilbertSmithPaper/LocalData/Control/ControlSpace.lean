import Mathlib
import HilbertSmithPaper.LocalData.Control.ZplusAction
import HilbertSmithPaper.LocalData.Subgroups.PadicSubgroups

/-!
# The control space

For a local datum, the control space is `T = Z⁺ / H₁`, the type of orbits of `H₁ = p ℤ_p` acting
on `Z⁺` by the restricted action, with the quotient topology and quotient map `π : Z⁺ → T`.

## Encoding

`T` is a `def` for Mathlib's `AddAction.orbitRel.Quotient (padicSubgroup p 1) A.Zplus`; its
topology `HSP.LocalDatum.instTopologicalSpaceT` is the quotient topology, and `HSP.LocalDatum.π` is
`Quotient.mk`.
-/

namespace HSP

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The control space `T = Z⁺ / H₁` of a local datum: the `H₁`-orbits of the restricted action on
`Z⁺`. -/
def LocalDatum.T (A : LocalDatum p n D ρplus) : Type :=
  AddAction.orbitRel.Quotient (padicSubgroup p 1) A.Zplus

/-- The quotient topology on the control space. -/
instance LocalDatum.instTopologicalSpaceT (A : LocalDatum p n D ρplus) :
    TopologicalSpace A.T :=
  inferInstanceAs (TopologicalSpace (Quotient (AddAction.orbitRel (padicSubgroup p 1) A.Zplus)))

/-- The quotient map `π : Z⁺ → T`. -/
noncomputable def LocalDatum.π (A : LocalDatum p n D ρplus) : A.Zplus → A.T :=
  Quotient.mk _

end HSP
