import Mathlib
import HilbertSmithPaper.LocalData.Subgroups.PadicSubgroups

/-!
# The subgroups `H_j` form a basis at `0`

Each `H_j` is open and compact, `H_{j+1} ⊆ H_j`, and every neighbourhood of `0` in `ℤ_[p]` contains
some `H_j`.
-/

open Topology Metric

namespace HSP

private lemma padicSubgroup_eq_closedBall (p : ℕ) [Fact p.Prime] (j : ℕ) :
    (padicSubgroup p j : Set ℤ_[p]) = closedBall 0 ((p : ℝ) ^ (-(j : ℤ))) := by
  ext x
  rw [mem_closedBall, dist_zero_right, PadicInt.norm_le_pow_iff_mem_span_pow,
    Ideal.mem_span_singleton]
  rfl

private lemma padicSubgroup_eq_ball (p : ℕ) [Fact p.Prime] (j : ℕ) :
    (padicSubgroup p j : Set ℤ_[p]) = ball 0 ((p : ℝ) ^ (-(j : ℤ) + 1)) := by
  rw [padicSubgroup_eq_closedBall]
  ext x
  rw [mem_closedBall, mem_ball, dist_zero_right, PadicInt.norm_le_pow_iff_norm_lt_pow_add_one]

/-- The subgroups `H_j` are open and compact, nested, and form a basis of neighbourhoods of `0`. -/
theorem padicSubgroup_basis (p : ℕ) [Fact p.Prime] :
    (∀ j, IsOpen (padicSubgroup p j : Set ℤ_[p]) ∧ IsCompact (padicSubgroup p j : Set ℤ_[p])) ∧
      (∀ j, (padicSubgroup p (j + 1) : Set ℤ_[p]) ⊆ padicSubgroup p j) ∧
      ∀ u ∈ 𝓝 (0 : ℤ_[p]), ∃ j, (padicSubgroup p j : Set ℤ_[p]) ⊆ u := by
  refine ⟨fun j => ⟨?_, ?_⟩, fun j x hx => ?_, fun u hu => ?_⟩
  · rw [padicSubgroup_eq_ball]; exact isOpen_ball
  · rw [padicSubgroup_eq_closedBall]; exact isClosed_closedBall.isCompact
  · exact dvd_trans (pow_dvd_pow _ j.le_succ) hx
  · obtain ⟨ε, hε, hεu⟩ := Metric.mem_nhds_iff.1 hu
    have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hp)
    refine ⟨j, fun x hx => hεu ?_⟩
    rw [padicSubgroup_eq_closedBall, mem_closedBall] at hx
    rw [mem_ball]
    refine lt_of_le_of_lt hx ?_
    simpa [zpow_neg, inv_pow] using hj

end HSP
