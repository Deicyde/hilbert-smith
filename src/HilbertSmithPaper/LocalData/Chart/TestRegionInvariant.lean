import Mathlib
import HilbertSmithPaper.LocalData.Chart.TestRegion
import HilbertSmithPaper.LocalData.Chart.OpenTestRegion
import HilbertSmithPaper.LocalData.Chart.AveragedMapInvariant

/-!
# The test regions are invariant

For a local datum, `Z⁺` and `U⁺` are invariant under `ℤ_[p]`, because `F₀ (a +ᵥ x) = F₀ x`.
-/

namespace HSP

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- `Z⁺` and `U⁺` are invariant under the action of `ℤ_[p]` on `Ω`. -/
theorem LocalDatum.vadd_mem_Zplus_Uplus (A : LocalDatum p n D ρplus) :
    (∀ a : ℤ_[p], ∀ x ∈ A.Zplus, a +ᵥ x ∈ A.Zplus) ∧
      (∀ a : ℤ_[p], ∀ x ∈ A.Uplus, a +ᵥ x ∈ A.Uplus) :=
  ⟨fun a x hx => by
      change ‖A.F₀ (a +ᵥ x)‖ ≤ ρplus
      rw [A.F₀_vadd]
      exact hx,
    fun a x hx => by
      change ‖A.F₀ (a +ᵥ x)‖ < ρplus
      rw [A.F₀_vadd]
      exact hx⟩

end HSP
