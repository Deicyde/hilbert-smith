import Mathlib
import HilbertSmithPaper.Categories.Asymptotic.Propagation

/-!
# Relabelling changes propagation by the labelling errors

`prop_{μ,μ'}(u) ≤ prop_{l,l'}(u) + max_b d(l b, μ b) + max_{b'} d(l' b', μ' b')`, the maxima being
`Finset.sup` on `ℝ≥0` (an empty maximum is `0`).
-/

open scoped NNReal

namespace HSP

variable {X : Type*} [MetricSpace X] {B B' : Type*} [Fintype B] [Fintype B']

/-- Relabelling changes propagation by at most the two labelling errors:
`prop_{μ,μ'}(u) ≤ prop_{l,l'}(u) + max_b d(l b, μ b) + max_{b'} d(l' b', μ' b')`. -/
theorem prop_relabel_le (l μ : B → X) (l' μ' : B' → X) (u : Matrix B' B ℚ) :
    prop μ μ' u ≤ prop l l' u + Finset.univ.sup (fun b => nndist (l b) (μ b)) +
      Finset.univ.sup (fun b' => nndist (l' b') (μ' b')) := by
  unfold prop
  refine Finset.sup_le fun q hq => ?_
  replace hq := (Finset.mem_filter.1 hq).2
  have h1 : nndist (l' q.1) (l q.2) ≤
      (Finset.univ.filter fun q : B' × B => u q.1 q.2 ≠ 0).sup
        fun q => nndist (l' q.1) (l q.2) :=
    Finset.le_sup (f := fun q : B' × B => nndist (l' q.1) (l q.2)) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hq⟩)
  have h2 : nndist (l q.2) (μ q.2) ≤ Finset.univ.sup (fun b => nndist (l b) (μ b)) :=
    Finset.le_sup (f := fun b => nndist (l b) (μ b)) (Finset.mem_univ _)
  have h3 : nndist (l' q.1) (μ' q.1) ≤ Finset.univ.sup (fun b' => nndist (l' b') (μ' b')) :=
    Finset.le_sup (f := fun b' => nndist (l' b') (μ' b')) (Finset.mem_univ _)
  calc nndist (μ' q.1) (μ q.2)
      ≤ nndist (μ' q.1) (l' q.1) + nndist (l' q.1) (l q.2) + nndist (l q.2) (μ q.2) :=
        (nndist_triangle _ (l q.2) _).trans (by gcongr; exact nndist_triangle _ _ _)
    _ = nndist (l' q.1) (l q.2) + nndist (l q.2) (μ q.2) + nndist (l' q.1) (μ' q.1) := by
        rw [nndist_comm (μ' q.1)]; ring
    _ ≤ _ := by gcongr

end HSP
