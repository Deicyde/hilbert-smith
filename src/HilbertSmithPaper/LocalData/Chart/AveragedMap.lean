import Mathlib
import HilbertSmithPaper.LocalData.Chart.LocalDatum

/-!
# The averaged chart map

For a local datum, `F₀ : Ω → ℝⁿ` is the average of `a ↦ a +ᵥ x` over the Haar probability measure
`μ` of `ℤ_[p]`: `F₀ x = ∫ a, (a +ᵥ x) ∂μ`.

## Encoding

Mathlib puts no measurable structure on `ℤ_[p]`. This module gives it the Borel σ-algebra
(`HSP.measurableSpacePadicInt`, `HSP.borelSpacePadicInt`), and `μ = HSP.haarZp p` is Mathlib's
additive Haar measure normalized on the whole (compact) group, so `μ univ = 1`
(`HSP.isProbabilityMeasure_haarZp`). These companions realize the article's "Haar probability
measure on `ℤ_p`" and are used by the articles on the averaged map.
-/

open MeasureTheory

namespace HSP

variable {p : ℕ} [Fact p.Prime]

/-- The Borel σ-algebra on `ℤ_[p]`. -/
noncomputable instance measurableSpacePadicInt : MeasurableSpace ℤ_[p] := borel ℤ_[p]

instance borelSpacePadicInt : BorelSpace ℤ_[p] := ⟨rfl⟩

variable (p) in
/-- The Haar probability measure `μ` on `ℤ_[p]`: the additive Haar measure giving the whole
group measure `1`. -/
noncomputable def haarZp : Measure ℤ_[p] := Measure.addHaarMeasure ⊤

/-- `μ` is a probability measure. -/
instance isProbabilityMeasure_haarZp : IsProbabilityMeasure (haarZp p) :=
  ⟨by simpa [haarZp] using
    Measure.addHaarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts ℤ_[p]))⟩

/-- The averaged chart map `F₀ x = ∫ a, (a +ᵥ x) ∂μ` of a local datum, `μ` the Haar probability
measure on `ℤ_[p]`. -/
noncomputable def LocalDatum.F₀ {n : ℕ} {D ρplus : ℝ} (A : LocalDatum p n D ρplus) (x : A.Ω) :
    EuclideanSpace ℝ (Fin n) :=
  ∫ a, ((a +ᵥ x : A.Ω) : EuclideanSpace ℝ (Fin n)) ∂haarZp p

end HSP
