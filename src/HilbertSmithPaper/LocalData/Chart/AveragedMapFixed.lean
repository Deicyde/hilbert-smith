import Mathlib
import HilbertSmithPaper.LocalData.Chart.AveragedMap

/-!
# The averaged map at a fixed point

If `a +ᵥ x = x` for all `a`, then `F₀ x = x`: the integral of a constant against a probability
measure is that constant.
-/

open MeasureTheory

namespace HSP

/-- At a point fixed by all of `ℤ_[p]`, the averaged map is the identity. -/
theorem LocalDatum.F₀_of_fixed {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}
    (A : LocalDatum p n D ρplus) {x : A.Ω} (h : ∀ a : ℤ_[p], a +ᵥ x = x) : A.F₀ x = x := by
  simp [LocalDatum.F₀, h]

end HSP
