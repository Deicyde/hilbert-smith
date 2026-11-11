import Mathlib
import HilbertSmithPaper.LocalData.Subgroups.PadicSubgroups

/-!
# The kernel of reduction modulo `p^i`

The kernel of the reduction `q_i = PadicInt.toZModPow i : ℤ_[p] → ZMod (p ^ i)` is `H_i`.
-/

namespace HSP

/-- The kernel of reduction modulo `p^i` is `H_i = p^i ℤ_p`. -/
theorem ker_toZModPow_eq (p : ℕ) [Fact p.Prime] (i : ℕ) :
    (PadicInt.toZModPow i : ℤ_[p] →+* ZMod (p ^ i)).toAddMonoidHom.ker = padicSubgroup p i := by
  ext a
  rw [AddMonoidHom.mem_ker]
  change PadicInt.toZModPow i a = 0 ↔ (p : ℤ_[p]) ^ i ∣ a
  rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]

end HSP
