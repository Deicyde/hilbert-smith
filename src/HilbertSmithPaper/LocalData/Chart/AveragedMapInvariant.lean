import Mathlib
import HilbertSmithPaper.LocalData.Subgroups.HaarZp
import HilbertSmithPaper.LocalData.Chart.AveragedMap

/-!
# The averaged map is invariant

`F₀ (b +ᵥ x) = F₀ x`: `a +ᵥ (b +ᵥ x) = (a + b) +ᵥ x`, and the Haar measure is invariant under
translation (left-invariant, hence right-invariant on the commutative group `ℤ_[p]`).
-/

open MeasureTheory

namespace HSP

/-- The averaged map is invariant under the action of `ℤ_[p]`. -/
theorem LocalDatum.F₀_vadd {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}
    (A : LocalDatum p n D ρplus) (b : ℤ_[p]) (x : A.Ω) : A.F₀ (b +ᵥ x) = A.F₀ x := by
  simp only [LocalDatum.F₀, haarZp, vadd_vadd]
  exact integral_add_right_eq_self
    (fun a : ℤ_[p] => ((a +ᵥ x : A.Ω) : EuclideanSpace ℝ (Fin n))) b

end HSP
