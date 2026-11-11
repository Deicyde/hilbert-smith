import Mathlib
import HilbertSmithPaper.Categories.Asymptotic.Propagation

/-!
# Propagation of a transpose

`prop(uᵀ) = prop(u)`, where `uᵀ` takes the labels of `B'` on its source and those of `B` on its
target: the entries are the same and the metric is symmetric.
-/

open scoped NNReal

namespace HSP

variable {X : Type*} [MetricSpace X] {B B' : Type*} [Fintype B] [Fintype B']

private theorem prop_transpose_le (l : B → X) (l' : B' → X) (u : Matrix B' B ℚ) :
    prop l' l u.transpose ≤ prop l l' u := by
  unfold prop
  refine Finset.sup_le fun q hq => ?_
  replace hq := (Finset.mem_filter.1 hq).2
  simp only [Matrix.transpose_apply] at hq
  rw [nndist_comm]
  exact Finset.le_sup (f := fun q : B' × B => nndist (l' q.1) (l q.2)) (b := (q.2, q.1))
    (Finset.mem_filter.2 ⟨Finset.mem_univ _, hq⟩)

/-- Propagation of a transpose: `prop(uᵀ) = prop(u)`, with the labels `l'` of `B'` on the source
of `uᵀ` and the labels `l` of `B` on its target. -/
theorem prop_transpose (l : B → X) (l' : B' → X) (u : Matrix B' B ℚ) :
    prop l' l u.transpose = prop l l' u :=
  le_antisymm (prop_transpose_le l l' u) (by simpa using prop_transpose_le l' l u.transpose)

end HSP
