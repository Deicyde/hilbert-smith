import Mathlib
import HilbertSmithPaper.LocalData.Subgroups.HaarZp
import HilbertSmithPaper.LocalData.Chart.AveragedMap

/-!
# The averaged map is continuous

`F₀` is a parametric integral, over the compact group `ℤ_[p]` with its finite Haar measure, of the
jointly continuous `(x, a) ↦ a +ᵥ x`, hence continuous on `Ω`.
-/

open MeasureTheory

namespace HSP

/-- The averaged map `F₀ : Ω → ℝⁿ` is continuous. -/
theorem LocalDatum.continuous_F₀ {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}
    (A : LocalDatum p n D ρplus) : Continuous A.F₀ := by
  have : LocallyCompactSpace A.Ω := A.isOpen_Ω.locallyCompactSpace
  have hf : Continuous (Function.uncurry fun (x : A.Ω) (a : ℤ_[p]) =>
      ((a +ᵥ x : A.Ω) : EuclideanSpace ℝ (Fin n))) :=
    continuous_subtype_val.comp (continuous_vadd.comp continuous_swap)
  have := continuous_parametric_integral_of_continuous (μ := haarZp p) hf isCompact_univ
  have h3 : Continuous fun x : A.Ω =>
      ∫ a, ((a +ᵥ x : A.Ω) : EuclideanSpace ℝ (Fin n)) ∂haarZp p := by
    simpa [Measure.restrict_univ] using this
  exact h3

end HSP
