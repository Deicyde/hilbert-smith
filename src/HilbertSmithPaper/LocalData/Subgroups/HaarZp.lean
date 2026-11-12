import Mathlib

/-!
# The Haar probability measure on `ℤ_p`

`ℤ_p` carries the Borel σ-algebra of its topology, and `μ` is the Haar measure of the compact group
`ℤ_p` normalized so that `μ(ℤ_p) = 1`.

## Encoding

Mathlib puts no measurable structure on `ℤ_[p]` (nor on `ℚ_[p]`), so the Borel instance
`HSP.measurableSpacePadicInt` (with `HSP.borelSpacePadicInt`) does not clash with one. `μ` is
`HSP.haarZp p` (the declaration of the article), Mathlib's additive Haar measure normalized on the
whole group, and `HSP.isProbabilityMeasure_haarZp` records `μ univ = 1`.
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

end HSP
