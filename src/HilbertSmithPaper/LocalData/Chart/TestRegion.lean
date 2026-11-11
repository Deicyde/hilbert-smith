import Mathlib
import HilbertSmithPaper.LocalData.Chart.AveragedMap

/-!
# The test region

For a local datum, the test region is `Z⁺ = {x ∈ Ω : |F₀ x| ≤ ρplus}`, a subset of the subtype `Ω`
so that the action of `ℤ_[p]` on `Ω` restricts to it directly.
-/

namespace HSP

/-- The test region `Z⁺ = {x ∈ Ω : |F₀ x| ≤ ρplus}` of a local datum. -/
def LocalDatum.Zplus {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ} (A : LocalDatum p n D ρplus) :
    Set A.Ω :=
  {x | ‖A.F₀ x‖ ≤ ρplus}

end HSP
