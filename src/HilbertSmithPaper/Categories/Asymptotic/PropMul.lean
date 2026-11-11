import Mathlib
import HilbertSmithPaper.Categories.Asymptotic.Propagation

/-!
# Propagation of a product

`prop(v u) ≤ prop(v) + prop(u)`: a nonzero entry `(v u)_{c a}` needs some `b` with
`v_{c b} u_{b a} ≠ 0`, and the triangle inequality through `l' b` gives the bound.
-/

open scoped NNReal

namespace HSP

variable {X : Type*} [MetricSpace X] {B B' B'' : Type*} [Fintype B] [Fintype B'] [Fintype B'']

/-- Propagation of a product: for `u ∈ ℚ^{B' × B}` and `v ∈ ℚ^{B'' × B'}` with labels
`l, l', l''` on `B, B', B''`, `prop(v u) ≤ prop(v) + prop(u)`. -/
theorem prop_mul_le (l : B → X) (l' : B' → X) (l'' : B'' → X) (u : Matrix B' B ℚ)
    (v : Matrix B'' B' ℚ) :
    prop l l'' (v * u) ≤ prop l' l'' v + prop l l' u := by
  unfold prop
  refine Finset.sup_le fun q hq => ?_
  replace hq := (Finset.mem_filter.1 hq).2
  simp only [Matrix.mul_apply] at hq
  obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq
  have hv : v q.1 b ≠ 0 := left_ne_zero_of_mul hb
  have hu : u b q.2 ≠ 0 := right_ne_zero_of_mul hb
  calc nndist (l'' q.1) (l q.2) ≤ nndist (l'' q.1) (l' b) + nndist (l' b) (l q.2) :=
        nndist_triangle _ _ _
    _ ≤ _ := add_le_add
        (Finset.le_sup (f := fun q : B'' × B' => nndist (l'' q.1) (l' q.2))
          (s := Finset.univ.filter fun q : B'' × B' => v q.1 q.2 ≠ 0) (b := (q.1, b))
          (Finset.mem_filter.2 ⟨Finset.mem_univ _, hv⟩))
        (Finset.le_sup (f := fun q : B' × B => nndist (l' q.1) (l q.2))
          (s := Finset.univ.filter fun q : B' × B => u q.1 q.2 ≠ 0) (b := (b, q.2))
          (Finset.mem_filter.2 ⟨Finset.mem_univ _, hu⟩))

end HSP
