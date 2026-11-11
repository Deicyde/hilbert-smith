import Mathlib
import HilbertSmithPaper.LocalData.Subgroups.ClosedSubgroups

/-!
# Proper closed subgroups lie in `p ℤ_p`

A closed additive subgroup `K ≠ ℤ_[p]` is `0` or some `H_j` with `j ≥ 1` (as `H_0 = ℤ_[p]`), hence
`K ⊆ H_1`.
-/

namespace HSP

/-- A proper closed additive subgroup of `ℤ_[p]` is contained in `H_1`. -/
theorem le_padicSubgroup_one_of_ne_top {p : ℕ} [Fact p.Prime] {K : AddSubgroup ℤ_[p]}
    (hK : IsClosed (K : Set ℤ_[p])) (h : K ≠ ⊤) : K ≤ padicSubgroup p 1 := by
  by_cases h0 : K = ⊥
  · rw [h0]
    exact bot_le
  obtain ⟨j, rfl⟩ := closed_eq_padicSubgroup K hK h0
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    exact absurd (eq_top_iff.2 fun x _ => by simp [padicSubgroup]) h
  · intro x hx
    exact dvd_trans (pow_dvd_pow _ hj) hx

end HSP
