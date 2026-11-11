import Mathlib
import HilbertSmithPaper.Categories.Asymptotic.Propagation

/-!
# Propagation of the identity

For a finite set `B` with labels `l : B → X`, the identity matrix has propagation `0` (with the
labels `l` on its source and its target): its nonzero entries are the diagonal entries, which join
each label to itself.
-/

open scoped NNReal

namespace HSP

variable {X : Type*} [MetricSpace X] {B : Type*} [Fintype B] [DecidableEq B]

/-- Propagation of the identity: `prop(1) = 0`. -/
theorem prop_one (l : B → X) : prop l l (1 : Matrix B B ℚ) = 0 := by
  refine le_antisymm (Finset.sup_le fun q hq => ?_) zero_le
  have h := (Finset.mem_filter.1 hq).2
  rw [Matrix.one_apply] at h
  split_ifs at h with hq'
  · rw [hq', nndist_self]
  · exact absurd rfl h

end HSP
