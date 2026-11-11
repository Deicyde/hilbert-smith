import Mathlib
import HilbertSmithPaper.Categories.Asymptotic.Propagation

/-!
# Propagation of a sum

`prop(u + v) ≤ max(prop u, prop v)`: a nonzero entry of `u + v` is a nonzero entry of `u` or
of `v`.
-/

open scoped NNReal

namespace HSP

variable {X : Type*} [MetricSpace X] {B B' : Type*} [Fintype B] [Fintype B']

/-- Propagation of a sum: `prop(u + v) ≤ max(prop u, prop v)`. -/
theorem prop_add_le (l : B → X) (l' : B' → X) (u v : Matrix B' B ℚ) :
    prop l l' (u + v) ≤ max (prop l l' u) (prop l l' v) := by
  unfold prop
  refine Finset.sup_le fun q hq => ?_
  replace hq := (Finset.mem_filter.1 hq).2
  simp only [Matrix.add_apply] at hq
  by_cases hu : u q.1 q.2 = 0
  · have hv : v q.1 q.2 ≠ 0 := by simpa [hu] using hq
    exact le_max_of_le_right
      (Finset.le_sup (f := fun q : B' × B => nndist (l' q.1) (l q.2)) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hv⟩))
  · exact le_max_of_le_left
      (Finset.le_sup (f := fun q : B' × B => nndist (l' q.1) (l q.2)) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hu⟩))

end HSP
