import Mathlib
import HilbertSmithPaper.LocalData.Chart.AveragedMap
import HilbertSmithPaper.LocalData.Chart.Pinch

/-!
# The test map

For a local datum and a radius `ρ`, the test map `f : Sⁿ → Sⁿ` (`Sⁿ = OnePoint ℝⁿ`) is
`f x = σ_ρ (F₀ x)` for `x ∈ Ω`, `f x = ∞` for `x ∈ ℝⁿ \ Ω`, and `f ∞ = ∞`. The definition makes
sense for every real `ρ`; the paper uses it for `0 < ρ < ρplus`.
-/

open OnePoint

namespace HSP

open Classical in
/-- The test map `f : Sⁿ → Sⁿ` of radius `ρ`: `σ_ρ ∘ F₀` on `Ω`, and `∞` elsewhere. -/
noncomputable def LocalDatum.testMap {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}
    (A : LocalDatum p n D ρplus) (ρ : ℝ) :
    OnePoint (EuclideanSpace ℝ (Fin n)) → OnePoint (EuclideanSpace ℝ (Fin n)) :=
  fun x => x.elim ∞ fun v =>
    if h : v ∈ A.Ω then pinch ρ (A.F₀ ⟨v, h⟩ : OnePoint (EuclideanSpace ℝ (Fin n))) else ∞

end HSP
