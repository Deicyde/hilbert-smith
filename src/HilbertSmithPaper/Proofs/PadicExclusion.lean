import HilbertSmithPaper.Proofs.OneChart
import HilbertSmithPaper.Proofs.LocalExclusion

/-!
# `p`-adic exclusion

No faithful jointly continuous action of the `p`-adic integers on a connected topological
manifold (Hausdorff, charted on `ℝⁿ`, no countability assumption). The binders and conclusion are
exactly those of Formal Conjectures' `Hilbert5.hilbert_smith_padic_formulation`
(google-deepmind/formal-conjectures, Apache-2.0), in the same order, so that a file stating that
formulation closes by `exact`.

The action of the additive group `ℤ_[p]` is Mathlib's `AddAction`, joint continuity is
`ContinuousVAdd`, and faithfulness is `FaithfulVAdd`.

Proof: a faithful action gives, by the reduction to one chart (`HSP.oneChart`), a faithful
jointly continuous action on a nonempty connected open subset of `ℝⁿ`, which local exclusion
(`HSP.localExclusion`) rules out. Both are open statements for now, so this proof is conditional.
-/

namespace HSP

/-- **`p`-adic exclusion.** A jointly continuous action of `ℤ_[p]` on a connected Hausdorff
space charted on `ℝⁿ` is not faithful. -/
theorem padicExclusion {n : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] (p : ℕ) [Fact p.Prime] [AddAction ℤ_[p] X]
    [ContinuousVAdd ℤ_[p] X] : ¬ FaithfulVAdd ℤ_[p] X := by
  intro hf
  obtain ⟨O, hO, hc, _, _, hfO⟩ := oneChart (n := n) (M := X) p
  exact localExclusion p n O hO hc hfO

end HSP
