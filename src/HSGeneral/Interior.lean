import HSFormal.BoundaryReduction
import HilbertSmith.Topology.InvariantOpens

/-!
# From manifolds with boundary to their interiors

A continuous faithful action on a connected manifold with boundary restricts to a continuous
faithful action on its topological interior, which is a connected manifold without boundary. So
any statement proved for faithful actions on connected manifolds without boundary also holds for
manifolds with boundary (`HSGeneral.of_faithfulSMul_topInterior`). No second countability is
involved, and the manifold may lie in any universe.

The interior and its facts come from HS_proof: `HSFormal.topInterior`,
`HSFormal.isOpen_topInterior`, `HSFormal.topInteriorChartedSpace`, `HSFormal.dense_topInterior`,
`HSFormal.isPreconnected_of_dense_of_local`, `HSFormal.exists_isPreconnected_inter_topInterior`
and `HSFormal.smul_mem_topInterior`. The restricted action is
`HilbertSmith.invariantMulAction`.
-/

open Set TopologicalSpace

universe u v

namespace HSGeneral

/-- **Transfer to the interior.** Let a group `G` act continuously and faithfully on a connected
Hausdorff manifold `X` with boundary, of dimension `n + 1`. Then any statement `P` that holds
whenever `G` acts continuously and faithfully on a connected Hausdorff manifold of dimension
`n + 1` without boundary, in the universe of `X`, holds. The manifold used is the topological
interior of `X`. -/
@[to_additive
  /-- **Transfer to the interior.** Let an additive group `G` act continuously and faithfully on
  a connected Hausdorff manifold `X` with boundary, of dimension `n + 1`. Then any statement `P`
  that holds whenever `G` acts continuously and faithfully on a connected Hausdorff manifold of
  dimension `n + 1` without boundary, in the universe of `X`, holds. -/]
theorem of_faithfulSMul_topInterior {n : ℕ} {X : Type u} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [ChartedSpace (EuclideanHalfSpace (n + 1)) X]
    {G : Type v} [Group G] [TopologicalSpace G] [MulAction G X] [ContinuousSMul G X]
    [FaithfulSMul G X] {P : Prop}
    (h : ∀ (Y : Type u) [TopologicalSpace Y] [T2Space Y]
      [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) Y] [ConnectedSpace Y] [MulAction G Y]
      [ContinuousSMul G Y] [FaithfulSMul G Y], P) : P := by
  let I : Opens X := ⟨HSFormal.topInterior (n + 1) X, HSFormal.isOpen_topInterior⟩
  have hdense : Dense (I : Set X) := HSFormal.dense_topInterior
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) I :=
    HSFormal.topInteriorChartedSpace (n + 1) X
  -- The interior is dense, and near each point it meets a small open set in a preconnected set.
  have : ConnectedSpace I := isConnected_iff_connectedSpace.mp ⟨hdense.nonempty,
    HSFormal.isPreconnected_of_dense_of_local hdense
      HSFormal.exists_isPreconnected_inter_topInterior⟩
  have hinv : ∀ g : G, ∀ x ∈ I, g • x ∈ I := fun g _ hx => HSFormal.smul_mem_topInterior g hx
  let _ := HilbertSmith.invariantMulAction I hinv
  have := HilbertSmith.continuousSMul_invariantMulAction I hinv
  -- Two elements that agree on the dense set `I` agree everywhere, so they are equal.
  have := HilbertSmith.faithfulSMul_invariantMulAction I hinv fun g₁ g₂ hg =>
    eq_of_smul_eq_smul (α := X) fun x =>
      congrFun ((continuous_const_smul g₁).ext_on hdense (continuous_const_smul g₂) hg) x
  exact h I

end HSGeneral
