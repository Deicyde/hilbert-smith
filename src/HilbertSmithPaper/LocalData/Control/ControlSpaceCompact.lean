import Mathlib
import HilbertSmithPaper.LocalData.Control.ControlSpace
import HilbertSmithPaper.LocalData.Chart.TestRegionCompact

/-!
# The control space is compact

For a local datum, the control space `T` is compact in the quotient topology: it is the image of
the compact `Z⁺` under the continuous quotient map. The statement is registered as an instance.
-/

namespace HSP

/-- The control space of a local datum is compact. -/
theorem LocalDatum.compactSpace_T {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}
    (A : LocalDatum p n D ρplus) : CompactSpace A.T := by
  have : CompactSpace A.Zplus := isCompact_iff_compactSpace.1 A.isCompact_Zplus
  exact Quotient.compactSpace

attribute [instance] LocalDatum.compactSpace_T

end HSP
