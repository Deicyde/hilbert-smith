import Mathlib

/-!
# A faithfully acting group has no small subgroups

A locally compact topological group acting jointly continuously and faithfully on a connected
`n`-manifold (Hausdorff, charted on `ℝⁿ`) has a neighbourhood of `1` containing no subgroup other
than `⊥`. No countability is assumed on `M` or `G`, and no separation on `G`. `n` and `M` are
explicit, since the conclusion mentions only `G`.

The statement is in place; its proof is still `sorry`.
-/

open scoped Topology

namespace HSP

universe u v

/-- **No small subgroups.** A locally compact topological group acting jointly continuously and
faithfully on a connected `n`-manifold has a neighbourhood of `1` containing no subgroup other
than the trivial one. -/
theorem noSmallSubgroups (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M]
    [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (G : Type v) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [MulAction G M]
    [ContinuousSMul G M] [FaithfulSMul G M] :
    ∃ U ∈ 𝓝 (1 : G), ∀ H : Subgroup G, (H : Set G) ⊆ U → H = ⊥ := by
  sorry

end HSP
