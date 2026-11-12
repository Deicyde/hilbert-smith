import HilbertSmithPaper.Proofs.FaithfulHausdorff
import HilbertSmithPaper.Proofs.NoSmallSubgroups
import HilbertSmithPaper.Inputs.GleasonYamabe.GleasonYamabe

/-!
# Hilbert–Smith

A locally compact topological group acting jointly continuously and faithfully on a connected
`n`-manifold (Hausdorff, charted on `ℝⁿ`) is a Lie group: for some `d` it carries an atlas of
charts onto open subsets of `ℝ^d`, for its given topology, making it a `C^∞` Lie group
(`LieGroup (𝓡 d) ∞ G` contains the smoothness of transition maps, multiplication and inversion).
Neither `M` nor `G` is assumed second countable, and `G` is not assumed Hausdorff. The conclusion
is the same as that of `HSP.gleasonYamabe`. `n` and `M` are explicit, since the conclusion
mentions only `G`.

Proof: `G` is Hausdorff (`HSP.t2Space_of_faithfulSMul`) and has no small subgroups
(`HSP.noSmallSubgroups`), so Gleason–Yamabe (`HSP.gleasonYamabe`) applies.
-/

open scoped ContDiff Manifold

namespace HSP

universe u v

/-- **Hilbert–Smith.** A locally compact topological group acting jointly continuously and
faithfully on a connected `n`-manifold carries, for some `d`, an atlas of charts onto open
subsets of `ℝ^d` making it a `C^∞` Lie group. -/
theorem hilbertSmith (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (G : Type v) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [MulAction G M] [ContinuousSMul G M]
    [FaithfulSMul G M] :
    ∃ (d : ℕ) (_ : ChartedSpace (EuclideanSpace ℝ (Fin d)) G), LieGroup (𝓡 d) ∞ G := by
  have := t2Space_of_faithfulSMul (Q := G) (X := M)
  exact gleasonYamabe G (noSmallSubgroups n M G)

end HSP
