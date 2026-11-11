import Mathlib
import HilbertSmithPaper.LocalData.Chart.TestRegion
import HilbertSmithPaper.LocalData.Chart.OpenTestRegion

/-!
# The test regions are invariant

For a local datum, `Z⁺` and `U⁺` are invariant under `ℤ_[p]`.

## Companion

The restricted action of `ℤ_[p]` on `Z⁺` (`HSP.LocalDatum.instAddActionZplus`, with
`HSP.LocalDatum.coe_vadd_Zplus`) is built here from the invariance of `Z⁺`; the orbit sup-distance,
its invariance and the control space use it.
-/

namespace HSP

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- `Z⁺` and `U⁺` are invariant under the action of `ℤ_[p]` on `Ω`. -/
theorem LocalDatum.vadd_mem_Zplus_Uplus (A : LocalDatum p n D ρplus) :
    (∀ a : ℤ_[p], ∀ x ∈ A.Zplus, a +ᵥ x ∈ A.Zplus) ∧
      (∀ a : ℤ_[p], ∀ x ∈ A.Uplus, a +ᵥ x ∈ A.Uplus) := by
  sorry

/-- The action of `ℤ_[p]` on `Ω` restricted to the invariant set `Z⁺`. -/
instance LocalDatum.instAddActionZplus (A : LocalDatum p n D ρplus) :
    AddAction ℤ_[p] A.Zplus where
  vadd a z := ⟨a +ᵥ (z : A.Ω), A.vadd_mem_Zplus_Uplus.1 a z z.2⟩
  zero_vadd z := Subtype.ext (zero_vadd ℤ_[p] (z : A.Ω))
  add_vadd a b z := Subtype.ext (add_vadd a b (z : A.Ω))

@[simp]
theorem LocalDatum.coe_vadd_Zplus (A : LocalDatum p n D ρplus) (a : ℤ_[p]) (z : A.Zplus) :
    ((a +ᵥ z : A.Zplus) : A.Ω) = a +ᵥ (z : A.Ω) :=
  rfl

end HSP
