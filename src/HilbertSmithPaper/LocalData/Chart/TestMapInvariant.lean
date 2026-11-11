import Mathlib
import HilbertSmithPaper.LocalData.Chart.TestMap
import HilbertSmithPaper.LocalData.Chart.AveragedMapInvariant

/-!
# The test map is invariant

`f (a +ᵥ x) = f x` for `a ∈ ℤ_[p]` and `x ∈ Ω`, because `F₀` is invariant. Points of `Ω` are viewed
in `Sⁿ` through `Ω → ℝⁿ → OnePoint ℝⁿ`. No condition on the radius `ρ` is needed.
-/

namespace HSP

/-- The test map is invariant under the action of `ℤ_[p]` on `Ω`. -/
theorem LocalDatum.testMap_vadd {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}
    (A : LocalDatum p n D ρplus) (ρ : ℝ) (a : ℤ_[p]) (x : A.Ω) :
    A.testMap ρ (((a +ᵥ x : A.Ω) : EuclideanSpace ℝ (Fin n)) :
      OnePoint (EuclideanSpace ℝ (Fin n))) =
      A.testMap ρ ((x : EuclideanSpace ℝ (Fin n)) : OnePoint (EuclideanSpace ℝ (Fin n))) := by
  simp [LocalDatum.testMap, A.F₀_vadd]

end HSP
