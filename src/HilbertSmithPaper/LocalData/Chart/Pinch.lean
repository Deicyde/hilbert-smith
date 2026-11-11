import Mathlib

/-!
# The pinch map

`σ_ρ : Sⁿ → Sⁿ` on the one-point compactification `Sⁿ = OnePoint ℝⁿ` of
`ℝⁿ = EuclideanSpace ℝ (Fin n)`: `σ_ρ(x) = x / (ρ - |x|)` for `|x| < ρ`, and `∞` otherwise.
The definition makes sense for every real `ρ`; the paper uses it for `ρ > 0`.
-/

open OnePoint

namespace HSP

/-- The *pinch* `σ_ρ : Sⁿ → Sⁿ`: `x ↦ (ρ - |x|)⁻¹ • x` on the open ball of radius `ρ`, and `∞` on
the rest of `ℝⁿ` and at `∞`. -/
noncomputable def pinch {n : ℕ} (ρ : ℝ) :
    OnePoint (EuclideanSpace ℝ (Fin n)) → OnePoint (EuclideanSpace ℝ (Fin n)) :=
  fun x => x.elim ∞ fun v =>
    if ‖v‖ < ρ then ((ρ - ‖v‖)⁻¹ • v : EuclideanSpace ℝ (Fin n)) else ∞

end HSP
