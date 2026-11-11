import Mathlib

/-!
# Faithful actions give Hausdorff groups

If `g` lies in the closure of `{1}`, then for each `x` continuity of `h ↦ h • x` puts `g • x`
in the closure of `{x}`, which is `{x}` in a `T₁` space; faithfulness gives `g = 1`. So `{1}` is
closed, and a topological group with closed identity is Hausdorff.
-/

namespace HSP

/-- A topological group acting jointly continuously and faithfully on a `T₁` space is
Hausdorff. -/
theorem t2Space_of_faithfulSMul {Q X : Type*} [Group Q] [TopologicalSpace Q]
    [IsTopologicalGroup Q] [TopologicalSpace X] [T1Space X] [MulAction Q X] [ContinuousSMul Q X]
    [FaithfulSMul Q X] : T2Space Q := by
  refine IsTopologicalGroup.t2Space_iff_one_closed.2 (closure_subset_iff_isClosed.1 ?_)
  intro g hg
  refine Set.mem_singleton_iff.2 (eq_of_smul_eq_smul (α := X) fun x => ?_)
  have : g • x ∈ closure ({x} : Set X) :=
    map_mem_closure (f := fun h : Q => h • x) (continuous_id.smul continuous_const) hg
      (by simp [Set.MapsTo])
  rw [closure_singleton, Set.mem_singleton_iff] at this
  rw [this, one_smul]

end HSP
