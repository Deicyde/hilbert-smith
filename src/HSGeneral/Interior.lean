import HSFormal.BoundaryReduction

/-!
# From manifolds with boundary to their interiors

A continuous faithful action on a connected manifold with boundary restricts to a continuous
faithful action on its topological interior, which is a connected manifold without boundary. So
any statement proved for faithful actions on connected manifolds without boundary also holds for
manifolds with boundary (`HSGeneral.of_faithfulSMul_topInterior`). No second countability is
involved, and the manifold may lie in any universe.

The interior, its charts and the restricted action come from HS_proof: `HSFormal.topInterior`,
`HSFormal.topInteriorChartedSpace`, `HSFormal.dense_topInterior`,
`HSFormal.isPreconnected_of_dense_of_local`, `HSFormal.exists_isPreconnected_inter_topInterior`,
`HSFormal.topInteriorMulAction`, `HSFormal.topInterior_continuousSMul` and
`HSFormal.topInterior_faithfulSMul` (with their additive forms).
-/

universe u v

namespace HSGeneral

/-- The topological interior of a connected manifold with boundary is connected, in any universe.
This is the one-line application of `HSFormal.isPreconnected_of_dense_of_local` to
`HSFormal.dense_topInterior` and `HSFormal.exists_isPreconnected_inter_topInterior`; it is stated
here because `HSFormal.connectedSpace_topInterior` is stated for manifolds in `Type` only. -/
theorem connectedSpace_topInterior {d : ℕ} [NeZero d] {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanHalfSpace d) X] [ConnectedSpace X] :
    ConnectedSpace (HSFormal.topInterior d X) :=
  isConnected_iff_connectedSpace.mp ⟨HSFormal.dense_topInterior.nonempty,
    HSFormal.isPreconnected_of_dense_of_local HSFormal.dense_topInterior
      HSFormal.exists_isPreconnected_inter_topInterior⟩

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
      [ContinuousSMul G Y] [FaithfulSMul G Y], P) : P :=
  letI := HSFormal.topInteriorChartedSpace (n + 1) X
  have := connectedSpace_topInterior (d := n + 1) (X := X)
  letI := HSFormal.topInteriorMulAction (n + 1) X G
  have := HSFormal.topInterior_continuousSMul (d := n + 1) (M := X) (G := G)
  have := HSFormal.topInterior_faithfulSMul (d := n + 1) (M := X) (G := G)
    HSFormal.dense_topInterior
  h (HSFormal.topInterior (n + 1) X)

end HSGeneral
