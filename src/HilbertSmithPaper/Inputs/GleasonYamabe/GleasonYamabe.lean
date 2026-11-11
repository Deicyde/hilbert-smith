import Mathlib

/-!
# Gleason–Yamabe: no small subgroups implies Lie

A classical input, stated over Mathlib notions with a `sorry` proof (an open statement).
"No small subgroups" is a neighbourhood of `1` containing no subgroup other than `⊥`. The
conclusion is an atlas on `G` modelled on `EuclideanSpace ℝ (Fin d)` (a `ChartedSpace` for the
given topology of `G`) for which `G` is a `C^∞` Lie group: `LieGroup (𝓡 d) ∞ G` contains the
smoothness of the transition maps (`IsManifold`), of multiplication and of inversion. No
countability is assumed.
-/

open scoped ContDiff Manifold Topology

namespace HSP

universe v

/-- **Gleason–Yamabe** (classical, open statement). A Hausdorff locally compact topological group
with no small subgroups carries, for some `d`, an atlas of charts onto open subsets of `ℝ^d`
making it a `C^∞` Lie group. -/
theorem gleasonYamabe (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G]
    (hnss : ∃ U ∈ 𝓝 (1 : G), ∀ H : Subgroup G, (H : Set G) ⊆ U → H = ⊥) :
    ∃ (d : ℕ) (_ : ChartedSpace (EuclideanSpace ℝ (Fin d)) G), LieGroup (𝓡 d) ∞ G := by
  sorry

end HSP
