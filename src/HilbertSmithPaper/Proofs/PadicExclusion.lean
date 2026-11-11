import Mathlib

/-!
# `p`-adic exclusion

No faithful jointly continuous action of the `p`-adic integers on a connected topological
manifold (Hausdorff, charted on `ℝⁿ`, no countability assumption). The binders and conclusion are
exactly those of Formal Conjectures' `Hilbert5.hilbert_smith_padic_formulation`
(google-deepmind/formal-conjectures, Apache-2.0), in the same order, so that a file stating that
formulation closes by `exact`.

The action of the additive group `ℤ_[p]` is Mathlib's `AddAction`, joint continuity is
`ContinuousVAdd`, and faithfulness is `FaithfulVAdd`.
-/

namespace HSP

/-- **`p`-adic exclusion.** A jointly continuous action of `ℤ_[p]` on a connected Hausdorff
space charted on `ℝⁿ` is not faithful. -/
theorem padicExclusion {n : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] (p : ℕ) [Fact p.Prime] [AddAction ℤ_[p] X]
    [ContinuousVAdd ℤ_[p] X] : ¬ FaithfulVAdd ℤ_[p] X := by
  sorry

end HSP
