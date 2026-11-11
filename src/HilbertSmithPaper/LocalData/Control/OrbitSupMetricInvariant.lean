import Mathlib
import HilbertSmithPaper.LocalData.Control.OrbitSupMetric
import HilbertSmithPaper.LocalData.Control.ZplusAction

/-!
# The orbit sup-distance is invariant

`d₁ (b +ᵥ z) (b +ᵥ w) = d₁ z w` for `b ∈ ℤ_[p]` and `z, w ∈ Z⁺`, where `b +ᵥ z` is the restricted
action on `Z⁺`: reindex the supremum along `a ↦ a + b`.
-/

namespace HSP

/-- The orbit sup-distance is invariant under `ℤ_[p]`. -/
theorem LocalDatum.d₁_vadd {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}
    (A : LocalDatum p n D ρplus) (b : ℤ_[p]) (z w : A.Zplus) :
    A.d₁ (b +ᵥ z) (b +ᵥ w) = A.d₁ z w := by
  unfold LocalDatum.d₁
  simp only [LocalDatum.coe_vadd_Zplus, vadd_vadd]
  exact (Equiv.addRight b).iSup_comp
    (g := fun a : ℤ_[p] => dist ((a +ᵥ (z : A.Ω) : A.Ω) : EuclideanSpace ℝ (Fin n))
      ((a +ᵥ (w : A.Ω) : A.Ω) : EuclideanSpace ℝ (Fin n)))

end HSP
