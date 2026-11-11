import Mathlib

/-!
# The subgroup `P_i`

For `i ≥ 1`, `G_i = ZMod (p ^ i)` and `χ_i : G_i → C_p = ZMod p` is reduction modulo `p`
(`ZMod.castHom`, defined since `p ∣ p ^ i`); `P_i = ker χ_i`.
-/

namespace HSP

/-- The subgroup `P_i = ker (χ_i : ZMod (p ^ i) → ZMod p)` for `i ≥ 1`. -/
def sheetSubgroup (p : ℕ) [Fact p.Prime] (i : ℕ) (hi : 1 ≤ i) : AddSubgroup (ZMod (p ^ i)) :=
  (ZMod.castHom (dvd_pow_self p (by omega)) (ZMod p)).toAddMonoidHom.ker

end HSP
