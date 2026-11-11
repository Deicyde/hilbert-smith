import Mathlib
import HilbertSmithPaper.LocalData.Control.ControlAction
import HilbertSmithPaper.LocalData.Control.ControlMetric

/-!
# The cyclic action is isometric

`d_T (c +ᵥ s) (c +ᵥ t) = d_T s t` for `c ∈ C_p` and `s, t ∈ T`. With `c` acting through its
representative `a = c.val`, `b +ᵥ (a +ᵥ w) = a +ᵥ (b +ᵥ w)` and the invariance of `d₁` remove `a`.
-/

namespace HSP

/-- The cyclic action on the control space is isometric for `d_T`. -/
theorem LocalDatum.dT_vadd {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}
    (A : LocalDatum p n D ρplus) (c : ZMod p) (s t : A.T) :
    A.dT (c +ᵥ s) (c +ᵥ t) = A.dT s t := by
  induction s using Quotient.inductionOn' with
  | h z =>
    induction t using Quotient.inductionOn' with
    | h w =>
      change (⨅ b : padicSubgroup p 1,
          A.d₁ ((c.val : ℤ_[p]) +ᵥ z) ((b : ℤ_[p]) +ᵥ ((c.val : ℤ_[p]) +ᵥ w))) =
        ⨅ b : padicSubgroup p 1, A.d₁ z ((b : ℤ_[p]) +ᵥ w)
      refine iInf_congr fun b => ?_
      rw [show (b : ℤ_[p]) +ᵥ ((c.val : ℤ_[p]) +ᵥ w) = (c.val : ℤ_[p]) +ᵥ ((b : ℤ_[p]) +ᵥ w) by
        rw [vadd_vadd, vadd_vadd, add_comm], A.d₁_vadd]

end HSP
