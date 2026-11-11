import Mathlib
import HilbertSmithPaper.LocalData.Control.ControlAction
import HilbertSmithPaper.LocalData.Chart.StabilizersOnTestRegion
import HilbertSmithPaper.LocalData.Control.ReductionKernel

/-!
# The cyclic action is free

If `c +ᵥ t = t` with `t = π z`, then, with `a = c.val`, `a +ᵥ z = b +ᵥ z` for some `b ∈ H₁`, so
`a - b` fixes `z` and lies in `H₁` (stabilizers on the test region). Hence `a ∈ H₁`, the kernel of
reduction modulo `p`, and `c = 0`.
-/

namespace HSP

/-- The cyclic action on the control space is free. -/
theorem LocalDatum.free {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}
    (A : LocalDatum p n D ρplus) (c : ZMod p) (t : A.T) (h : c +ᵥ t = t) : c = 0 := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  induction t using Quotient.inductionOn' with
  | h z =>
  have h' : A.π ((c.val : ℤ_[p]) +ᵥ z) = A.π z := h
  obtain ⟨b, hb⟩ := Quotient.exact h'
  have hb' : ((b : ℤ_[p]) +ᵥ (z : A.Ω) : A.Ω) = (c.val : ℤ_[p]) +ᵥ (z : A.Ω) :=
    congrArg Subtype.val hb
  have hstab : (c.val : ℤ_[p]) - b ∈ AddAction.stabilizer ℤ_[p] (z : A.Ω) := by
    rw [AddAction.mem_stabilizer_iff]
    calc ((c.val : ℤ_[p]) - b) +ᵥ (z : A.Ω) = -(b : ℤ_[p]) +ᵥ ((c.val : ℤ_[p]) +ᵥ (z : A.Ω)) := by
          rw [vadd_vadd]; congr 1; abel
      _ = -(b : ℤ_[p]) +ᵥ ((b : ℤ_[p]) +ᵥ (z : A.Ω)) := by rw [hb']
      _ = z := by rw [vadd_vadd, neg_add_cancel, zero_vadd]
  have h1 : (c.val : ℤ_[p]) ∈ padicSubgroup p 1 := by
    have := (padicSubgroup p 1).add_mem (A.stabilizer_le z.2 hstab) b.2
    rwa [sub_add_cancel] at this
  rw [← ker_toZModPow_eq, AddMonoidHom.mem_ker] at h1
  change PadicInt.toZModPow 1 (c.val : ℤ_[p]) = 0 at h1
  rw [map_natCast, ZMod.natCast_eq_zero_iff, pow_one] at h1
  rw [← ZMod.natCast_zmod_val c, ZMod.natCast_eq_zero_iff]
  exact h1

end HSP
