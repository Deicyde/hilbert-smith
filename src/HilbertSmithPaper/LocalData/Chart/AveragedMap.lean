import Mathlib
import HilbertSmithPaper.LocalData.Chart.LocalDatum
import HilbertSmithPaper.LocalData.Subgroups.HaarZp

/-!
# The averaged chart map

For a local datum, `F₀ : Ω → ℝⁿ` is the average of `a ↦ a +ᵥ x` over the Haar probability measure
`μ` of `ℤ_[p]` (`HSP.haarZp p`): `F₀ x = ∫ a, (a +ᵥ x) ∂μ`.
-/

open MeasureTheory

namespace HSP

variable {p : ℕ} [Fact p.Prime]

/-- The averaged chart map `F₀ x = ∫ a, (a +ᵥ x) ∂μ` of a local datum, `μ` the Haar probability
measure on `ℤ_[p]`. -/
noncomputable def LocalDatum.F₀ {n : ℕ} {D ρplus : ℝ} (A : LocalDatum p n D ρplus) (x : A.Ω) :
    EuclideanSpace ℝ (Fin n) :=
  ∫ a, ((a +ᵥ x : A.Ω) : EuclideanSpace ℝ (Fin n)) ∂haarZp p

end HSP
