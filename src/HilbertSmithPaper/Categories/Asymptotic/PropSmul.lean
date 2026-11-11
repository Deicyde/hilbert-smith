import Mathlib
import HilbertSmithPaper.Categories.Asymptotic.Propagation

/-!
# Propagation of a scalar multiple

`prop(c u) ≤ prop(u)`: every nonzero entry of `c u` is a nonzero entry of `u`.
-/

open scoped NNReal

namespace HSP

variable {X : Type*} [MetricSpace X] {B B' : Type*} [Fintype B] [Fintype B']

/-- Propagation of a scalar multiple: `prop(c u) ≤ prop(u)` for `c ∈ ℚ`. -/
theorem prop_smul_le (l : B → X) (l' : B' → X) (c : ℚ) (u : Matrix B' B ℚ) :
    prop l l' (c • u) ≤ prop l l' u := by
  unfold prop
  refine Finset.sup_mono fun q hq => ?_
  rw [Finset.mem_filter] at hq ⊢
  exact ⟨hq.1, right_ne_zero_of_mul
    (by simpa only [Matrix.smul_apply, smul_eq_mul] using hq.2)⟩

end HSP
