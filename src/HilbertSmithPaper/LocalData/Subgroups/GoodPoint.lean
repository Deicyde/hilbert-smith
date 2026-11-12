import Mathlib
import HilbertSmithPaper.LocalData.Subgroups.FixedSets
import HilbertSmithPaper.LocalData.Subgroups.InteriorFixedSetClosed

/-!
# A point with no fixed neighbourhood

For a jointly continuous faithful action of `ℤ_[p]` on a connected `n`-manifold `M`, some point has
no neighbourhood fixed pointwise by any `H_j`.

## Encoding

An `n`-manifold is a Hausdorff space (`T2Space`) with an atlas of open partial homeomorphisms onto
open subsets of `ℝⁿ = EuclideanSpace ℝ (Fin n)` (`ChartedSpace`), with no countability assumption;
connected spaces are nonempty (`ConnectedSpace`). The action is `AddAction ℤ_[p] M` with
`ContinuousVAdd` (joint continuity) and `FaithfulVAdd`.

If every point had a neighbourhood fixed by some `H_j`, each `interior (Fix_j M)` would be closed
(interiors of fixed sets are closed), hence clopen; at some point of the nonempty `M` one of them is
nonempty, so it is `M`, and then `p^j ≠ 0` acts trivially, against faithfulness.
-/

open Topology

namespace HSP

/-- A faithful jointly continuous action of `ℤ_[p]` on a connected `n`-manifold has a point `x`
such that no `Fix_j(M)` is a neighbourhood of `x`. -/
theorem exists_good_point {p : ℕ} [Fact p.Prime] {n : ℕ} {M : Type*} [TopologicalSpace M]
    [T2Space M] [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [AddAction ℤ_[p] M] [ContinuousVAdd ℤ_[p] M] [FaithfulVAdd ℤ_[p] M] :
    ∃ x : M, ∀ j, fixSet p M j ∉ 𝓝 x := by
  by_contra hcon
  simp only [not_exists, not_forall, not_not] at hcon
  obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
  obtain ⟨j, hj⟩ := hcon x₀
  have hclopen : IsClopen (interior (fixSet p M j)) :=
    ⟨isClosed_interior_fixSet (n := n) hcon j, isOpen_interior⟩
  have huniv := hclopen.eq_univ ⟨x₀, mem_interior_iff_mem_nhds.2 hj⟩
  have hall : ∀ y : M, ((p : ℤ_[p]) ^ j) +ᵥ y = (0 : ℤ_[p]) +ᵥ y := fun y => by
    rw [zero_vadd]
    have hy : y ∈ fixSet p M j := interior_subset (huniv ▸ Set.mem_univ y)
    exact hy _ (dvd_refl _)
  exact pow_ne_zero j (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
    (FaithfulVAdd.eq_of_vadd_eq_vadd hall)

end HSP
