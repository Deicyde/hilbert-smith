import Mathlib
import HilbertSmithPaper.LocalData.Subgroups.FixedSets

/-!
# Fixed sets are closed

If `ℤ_[p]` acts on a Hausdorff space `X` with each element acting continuously
(`ContinuousConstVAdd`), then `Fix_j(X)` is closed: it is the intersection over `a ∈ H_j` of the
sets where the continuous maps `a +ᵥ ·` and the identity agree.
-/

namespace HSP

/-- Fixed sets of the `H_j` are closed in a Hausdorff space. -/
theorem isClosed_fixSet {p : ℕ} [Fact p.Prime] {X : Type*} [TopologicalSpace X] [T2Space X]
    [AddAction ℤ_[p] X] [ContinuousConstVAdd ℤ_[p] X] (j : ℕ) : IsClosed (fixSet p X j) := by
  have : fixSet p X j = ⋂ a ∈ padicSubgroup p j, {x : X | a +ᵥ x = x} := by
    ext x
    simp [fixSet]
  rw [this]
  exact isClosed_biInter fun a _ => isClosed_eq (continuous_const_vadd a) continuous_id

end HSP
