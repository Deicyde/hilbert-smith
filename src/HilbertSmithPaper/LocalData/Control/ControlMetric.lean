import Mathlib
import HilbertSmithPaper.LocalData.Control.ZplusAction
import HilbertSmithPaper.LocalData.Control.ControlSpace
import HilbertSmithPaper.LocalData.Control.OrbitSupMetricInvariant

/-!
# The orbit metric on the control space

For a local datum, `d_T (π z) (π w) = min_{b ∈ H₁} d₁ z (b +ᵥ w)`. It is written as an infimum over
`H₁` (attained, `H₁` being compact), lifted to `T × T` through `Quotient.lift₂`; the value does not
depend on the representatives because `d₁` is `ℤ_[p]`-invariant and `ℤ_[p]` is abelian.
-/

namespace HSP

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The orbit metric `d_T (π z) (π w) = inf_{b ∈ H₁} d₁ z (b +ᵥ w)` on the control space. -/
noncomputable def LocalDatum.dT (A : LocalDatum p n D ρplus) : A.T → A.T → ℝ :=
  Quotient.lift₂ (fun z w : A.Zplus => ⨅ b : padicSubgroup p 1, A.d₁ z ((b : ℤ_[p]) +ᵥ w))
    (by
      rintro z₁ w₁ z₂ w₂ ⟨c, rfl⟩ ⟨e, rfl⟩
      have key : ∀ b : padicSubgroup p 1,
          A.d₁ (c +ᵥ z₂) ((b : ℤ_[p]) +ᵥ (e +ᵥ w₂)) =
            A.d₁ z₂ (((b + (e - c) : padicSubgroup p 1) : ℤ_[p]) +ᵥ w₂) := by
        intro b
        rw [← A.d₁_vadd (-(c : ℤ_[p]))]
        congr 1
        · change -(c : ℤ_[p]) +ᵥ ((c : ℤ_[p]) +ᵥ z₂) = z₂
          rw [vadd_vadd, neg_add_cancel, zero_vadd]
        · change -(c : ℤ_[p]) +ᵥ ((b : ℤ_[p]) +ᵥ ((e : ℤ_[p]) +ᵥ w₂)) = _
          rw [vadd_vadd, vadd_vadd]
          congr 1
          push_cast
          abel
      exact (iInf_congr key).trans
        ((Equiv.addRight (e - c)).iInf_comp
          (g := fun b : padicSubgroup p 1 => A.d₁ z₂ ((b : ℤ_[p]) +ᵥ w₂))))

end HSP
