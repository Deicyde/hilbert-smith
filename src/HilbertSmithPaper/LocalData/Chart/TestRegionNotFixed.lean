import Mathlib
import HilbertSmithPaper.LocalData.Chart.TestRegion
import HilbertSmithPaper.LocalData.Chart.AveragedMapFixed

/-!
# No point of the test region is fixed

Every `z ∈ Z⁺` is moved by some `a ∈ ℤ_[p]`: a point fixed by all of `ℤ_[p]` has `F₀ z = z`, so
`|z| ≤ ρplus`, which the condition of no fixed points near the origin excludes.
-/

namespace HSP

/-- Every point of the test region is moved by some element of `ℤ_[p]`. -/
theorem LocalDatum.exists_moved_of_mem_Zplus {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}
    (A : LocalDatum p n D ρplus) {z : A.Ω} (hz : z ∈ A.Zplus) : ∃ a : ℤ_[p], a +ᵥ z ≠ z := by
  by_contra h
  simp only [not_exists, not_not] at h
  have hz' : ‖A.F₀ z‖ ≤ ρplus := hz
  rw [A.F₀_of_fixed h] at hz'
  obtain ⟨a, ha⟩ := A.exists_moved z hz'
  exact ha (h a)

end HSP
