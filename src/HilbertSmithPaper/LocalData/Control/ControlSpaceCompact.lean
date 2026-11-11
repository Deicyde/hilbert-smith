import Mathlib
import HilbertSmithPaper.LocalData.Control.ControlSpace

/-!
# The control space is compact

For a local datum, the control space `T` is compact in the quotient topology. The statement is
registered as an instance.
-/

namespace HSP

/-- The control space of a local datum is compact. -/
theorem LocalDatum.compactSpace_T {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}
    (A : LocalDatum p n D ρplus) : CompactSpace A.T := by
  sorry

attribute [instance] LocalDatum.compactSpace_T

end HSP
