import HilbertSmithPaper.Proofs.InteriorAction

/-!
# The restricted action is continuous

Joint continuity of the action of `G` on `M` passes to the invariant subspace `M°ₙ`: the action
map `G × M°ₙ → M°ₙ` is the action map of `M` composed with the inclusion, corestricted.
Only a topology on `G` is needed, no group topology.
-/

namespace HSP

/-- If `G` acts jointly continuously on `M`, the restricted action on `M°ₙ` is jointly
continuous. -/
@[to_additive /-- If `G` acts jointly continuously on `M`, the restricted action on `M°ₙ` is
jointly continuous. -/]
instance intrinsicInterior.continuousSMul {n : ℕ} {G M : Type*} [Group G] [TopologicalSpace G]
    [TopologicalSpace M] [MulAction G M] [ContinuousSMul G M] :
    ContinuousSMul G (intrinsicInterior n M) where
  continuous_smul :=
    (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)).subtype_mk _

end HSP
