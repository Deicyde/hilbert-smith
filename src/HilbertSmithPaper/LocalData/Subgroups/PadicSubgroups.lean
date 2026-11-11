import Mathlib

/-!
# The subgroups `H_j = p^j ℤ_p`

`H_j = {a ∈ ℤ_[p] : p^j ∣ a}` as an additive subgroup of `ℤ_[p]`.
-/

namespace HSP

/-- The subgroup `H_j = p^j ℤ_p = {a ∈ ℤ_[p] : p^j ∣ a}`. -/
def padicSubgroup (p : ℕ) [Fact p.Prime] (j : ℕ) : AddSubgroup ℤ_[p] where
  carrier := {a | (p : ℤ_[p]) ^ j ∣ a}
  add_mem' := dvd_add
  zero_mem' := dvd_zero _
  neg_mem' := (dvd_neg).2

end HSP
