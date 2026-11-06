import Mathlib.Geometry.Manifold.HasGroupoid
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Connected.LocallyConnected

/-!
# Invariant second-countable open subsets of a manifold

A continuous action on a connected manifold that is not second countable can often be replaced by
its restriction to a smaller invariant open set that is second countable. This file proves the
topology behind that reduction (HSproof.tex, the proof of Corollary 1.2). It imports Mathlib only.

## Main results

* `HilbertSmith.exists_isOpen_isConnected_mem_isCompact_closure`: in a locally connected, weakly
  locally compact R₁ space, every point has a connected open neighbourhood with compact closure.
* `HilbertSmith.exists_isOpen_isConnected_superset_isCompact_closure`: if the space is moreover
  connected, every compact set lies in a connected open set with compact closure.
* `HilbertSmith.exists_smul_invariant_opens_secondCountable`: let a monoid `G` act continuously on
  a connected Hausdorff space charted on a second-countable, locally compact, locally connected
  model. Given an increasing sequence of compact sets `K j ⊆ G` and any sequence of compact sets
  `C j` of the space, some connected, second-countable open set contains every `C j` and is mapped
  into itself by every element of every `K j`.
* `HilbertSmith.exists_subgroup_invariant_opens_secondCountable`: the same for a subgroup that is
  the union of an increasing sequence of compact sets; the open set is then mapped onto itself.
* `HilbertSmith.invariantMulAction`: the restriction of an action to an invariant open set, with
  `HilbertSmith.continuousSMul_invariantMulAction` and
  `HilbertSmith.faithfulSMul_invariantMulAction`.

All results have additive forms.

## Implementation notes

The invariant open set is built as an increasing union `⋃ j, V j` of connected open sets with
compact closures, where `V (j + 1)` contains `K j • closure (V j) ∪ closure (V j) ∪ C (j + 1)`.
It is σ-compact, so second countable by `ChartedSpace.secondCountable_of_sigmaCompact`.

The paper builds the neighbourhoods of the second step by joining finitely many charts with paths;
here they come from a clopen argument instead.
-/

open Set Topology TopologicalSpace Pointwise

namespace HilbertSmith

section Neighbourhoods

variable {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X] [WeaklyLocallyCompactSpace X]
  [R1Space X]

/-- In a locally connected, weakly locally compact R₁ space, every point has a connected open
neighbourhood with compact closure. -/
theorem exists_isOpen_isConnected_mem_isCompact_closure (x : X) :
    ∃ V : Set X, IsOpen V ∧ IsConnected V ∧ x ∈ V ∧ IsCompact (closure V) := by
  obtain ⟨N, hNo, hxN, hNc⟩ := exists_isOpen_mem_isCompact_closure x
  obtain ⟨V, hVN, hVo, hxV, hVc⟩ :=
    locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp ‹_› x N (hNo.mem_nhds hxN)
  exact ⟨V, hVo, hVc, hxV, hNc.of_isClosed_subset isClosed_closure (closure_mono hVN)⟩

/-- In a connected, locally connected, weakly locally compact R₁ space, every compact set lies in a
connected open set with compact closure. -/
theorem exists_isOpen_isConnected_superset_isCompact_closure [ConnectedSpace X] {C : Set X}
    (hC : IsCompact C) : ∃ V : Set X, IsOpen V ∧ IsConnected V ∧ C ⊆ V ∧ IsCompact (closure V) := by
  obtain ⟨x₀⟩ := ConnectedSpace.toNonempty (α := X)
  -- The points joined to `x₀` by a preconnected open set with compact closure form a clopen set.
  let W : Set X :=
    {y | ∃ V : Set X, IsOpen V ∧ IsPreconnected V ∧ x₀ ∈ V ∧ y ∈ V ∧ IsCompact (closure V)}
  have hW : W = univ := by
    refine IsClopen.eq_univ ⟨?_, ?_⟩ ?_
    · rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
      intro y hy
      obtain ⟨B, hBo, hBc, hyB, hBcl⟩ := exists_isOpen_isConnected_mem_isCompact_closure y
      refine ⟨B, fun z hzB hzW => hy ?_, hBo, hyB⟩
      obtain ⟨V, hVo, hVc, hx₀V, hzV, hVcl⟩ := hzW
      refine ⟨V ∪ B, hVo.union hBo, hVc.union z hzV hzB hBc.isPreconnected, .inl hx₀V, .inr hyB, ?_⟩
      rw [closure_union]
      exact hVcl.union hBcl
    · rw [isOpen_iff_forall_mem_open]
      rintro y ⟨V, hVo, hVc, hx₀V, hyV, hVcl⟩
      exact ⟨V, fun z hz => ⟨V, hVo, hVc, hx₀V, hz, hVcl⟩, hVo, hyV⟩
    · obtain ⟨B, hBo, hBc, hxB, hBcl⟩ := exists_isOpen_isConnected_mem_isCompact_closure x₀
      exact ⟨x₀, B, hBo, hBc.isPreconnected, hxB, hxB, hBcl⟩
  have key : ∀ y, y ∈ W := fun y => hW ▸ mem_univ y
  choose V hVo hVc hx₀V hyV hVcl using key
  -- Finitely many of these sets cover `C`; add the one around `x₀` in case `C` is empty.
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover V hVo fun y _ => mem_iUnion.2 ⟨y, hyV y⟩
  let s : Set X := insert x₀ t
  have hs : s.Finite := t.finite_toSet.insert x₀
  refine ⟨⋃ y ∈ s, V y, isOpen_biUnion fun y _ => hVo y, ⟨?_, ?_⟩, ?_, ?_⟩
  · exact ⟨x₀, mem_biUnion (mem_insert x₀ _) (hx₀V x₀)⟩
  · rw [biUnion_eq_iUnion]
    exact isPreconnected_iUnion ⟨x₀, mem_iInter.2 fun y => hx₀V y⟩ fun y => hVc y
  · exact ht.trans (biUnion_subset_biUnion_left (subset_insert x₀ _))
  · rw [hs.closure_biUnion]
    exact hs.isCompact_biUnion fun y _ => hVcl y

end Neighbourhoods

section Exhaustion

variable {H : Type*} [TopologicalSpace H] [SecondCountableTopology H] [LocallyCompactSpace H]
  [LocallyConnectedSpace H]
  {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace H X]

include H

/-- **Invariant second-countable open set.** Let a monoid `G` act continuously on a connected
Hausdorff space `X` charted on a second-countable, locally compact, locally connected model `H`
(for instance a connected topological manifold). Given an increasing sequence of compact sets
`K j ⊆ G` and any sequence of compact sets `C j ⊆ X`, some connected, second-countable open set `U`
contains every `C j` and is mapped into itself by every element of `⋃ j, K j`. -/
@[to_additive
  /-- **Invariant second-countable open set.** Let an additive monoid `G` act continuously on a
  connected Hausdorff space `X` charted on a second-countable, locally compact, locally connected
  model `H`. Given an increasing sequence of compact sets `K j ⊆ G` and any sequence of compact
  sets `C j ⊆ X`, some connected, second-countable open set `U` contains every `C j` and is mapped
  into itself by every element of `⋃ j, K j`. -/]
theorem exists_smul_invariant_opens_secondCountable {G : Type*} [Monoid G] [TopologicalSpace G]
    [MulAction G X] [ContinuousSMul G X] (K : ℕ → Set G) (hK : ∀ j, IsCompact (K j))
    (hKmono : Monotone K) (C : ℕ → Set X) (hC : ∀ j, IsCompact (C j)) :
    ∃ U : Opens X, IsConnected (U : Set X) ∧ SecondCountableTopology U ∧
      (∀ j, C j ⊆ U) ∧ ∀ g ∈ ⋃ j, K j, ∀ x ∈ U, g • x ∈ U := by
  have := ChartedSpace.locallyCompactSpace H X
  have := ChartedSpace.locallyConnectedSpace H X
  choose! F hFo hFc hFsub hFcl using
    fun (A : Set X) (hA : IsCompact A) => exists_isOpen_isConnected_superset_isCompact_closure hA
  -- `V (j + 1)` absorbs the compact set `K j • closure (V j) ∪ closure (V j) ∪ C (j + 1)`.
  let V : ℕ → Set X := fun j =>
    Nat.rec (F (C 0)) (fun j Vj => F (K j • closure Vj ∪ closure Vj ∪ C (j + 1))) j
  have hV0 : V 0 = F (C 0) := rfl
  have hVs : ∀ j, V (j + 1) = F (K j • closure (V j) ∪ closure (V j) ∪ C (j + 1)) := fun _ => rfl
  have hin : ∀ j, IsCompact (K j • closure (V j) ∪ closure (V j) ∪ C (j + 1)) ∧
      IsCompact (closure (V (j + 1))) := by
    have hcl : ∀ j, IsCompact (closure (V j)) →
        IsCompact (K j • closure (V j) ∪ closure (V j) ∪ C (j + 1)) := fun j h =>
      ((hK j).smul_set h).union h |>.union (hC (j + 1))
    intro j
    induction j with
    | zero => exact ⟨hcl 0 (hV0 ▸ hFcl _ (hC 0)), hVs 0 ▸ hFcl _ (hcl 0 (hV0 ▸ hFcl _ (hC 0)))⟩
    | succ j ih => exact ⟨hcl (j + 1) ih.2, hVs (j + 1) ▸ hFcl _ (hcl (j + 1) ih.2)⟩
  have hVo : ∀ j, IsOpen (V j) := by
    rintro (_ | j)
    · exact hFo _ (hC 0)
    · exact hFo _ (hin j).1
  have hVc : ∀ j, IsConnected (V j) := by
    rintro (_ | j)
    · exact hFc _ (hC 0)
    · exact hFc _ (hin j).1
  have hVsub : ∀ j, K j • closure (V j) ∪ closure (V j) ∪ C (j + 1) ⊆ V (j + 1) := fun j =>
    hFsub _ (hin j).1
  have hclV : ∀ j, closure (V j) ⊆ V (j + 1) := fun j =>
    subset_union_right.trans (subset_union_left.trans (hVsub j))
  have hVmono : Monotone V := monotone_nat_of_le_succ fun j => subset_closure.trans (hclV j)
  let U : Opens X := ⟨⋃ j, V j, isOpen_iUnion hVo⟩
  obtain ⟨x, hx⟩ := (hVc 0).nonempty
  refine ⟨U, ⟨⟨x, mem_iUnion.2 ⟨0, hx⟩⟩, ?_⟩, ?_, ?_, ?_⟩
  · exact isPreconnected_iUnion ⟨x, mem_iInter.2 fun j => hVmono (Nat.zero_le j) hx⟩
      fun j => (hVc j).isPreconnected
  · -- `U` is the union of the compact sets `closure (V j)`, so it is σ-compact.
    have hU : (U : Set X) = ⋃ j, closure (V j) :=
      Subset.antisymm (iUnion_mono fun j => subset_closure)
        (iUnion_subset fun j => (hclV j).trans (subset_iUnion V (j + 1)))
    have : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
      (hU ▸ isSigmaCompact_iUnion_of_isCompact _ fun j =>
        (Nat.casesOn j (hV0 ▸ hFcl _ (hC 0)) fun j => (hin j).2 : IsCompact (closure (V j))))
    exact ChartedSpace.secondCountable_of_sigmaCompact H U
  · rintro (_ | j)
    · exact (hFsub _ (hC 0)).trans (subset_iUnion V 0)
    · exact subset_union_right.trans ((hVsub j).trans (subset_iUnion V (j + 1)))
  · intro g hg y hy
    obtain ⟨m, hgm⟩ := mem_iUnion.1 hg
    obtain ⟨i, hyi⟩ := mem_iUnion.1 hy
    have hgk : g ∈ K (max m i) := hKmono (le_max_left m i) hgm
    have hyk : y ∈ closure (V (max m i)) := subset_closure (hVmono (le_max_right m i) hyi)
    exact mem_iUnion.2 ⟨max m i + 1, hVsub _ (.inl (.inl (smul_mem_smul hgk hyk)))⟩

/-- **Invariant second-countable open set, subgroup form.** Let a group `G` act continuously on a
connected Hausdorff space `X` charted on a second-countable, locally compact, locally connected
model `H`. If a subgroup `S` of `G` is the union of an increasing sequence of compact sets `K j`,
then for any sequence of compact sets `C j ⊆ X`, some connected, second-countable open set `U`
contains every `C j` and satisfies `g • U = U` for every `g ∈ S`. -/
@[to_additive
  /-- **Invariant second-countable open set, subgroup form.** Let an additive group `G` act
  continuously on a connected Hausdorff space `X` charted on a second-countable, locally compact,
  locally connected model `H`. If a subgroup `S` of `G` is the union of an increasing sequence of
  compact sets `K j`, then for any sequence of compact sets `C j ⊆ X`, some connected,
  second-countable open set `U` contains every `C j` and satisfies `g +ᵥ U = U` for every
  `g ∈ S`. -/]
theorem exists_subgroup_invariant_opens_secondCountable {G : Type*} [Group G] [TopologicalSpace G]
    [MulAction G X] [ContinuousSMul G X] (S : Subgroup G) (K : ℕ → Set G)
    (hK : ∀ j, IsCompact (K j)) (hKmono : Monotone K) (hS : (S : Set G) = ⋃ j, K j)
    (C : ℕ → Set X) (hC : ∀ j, IsCompact (C j)) :
    ∃ U : Opens X, IsConnected (U : Set X) ∧ SecondCountableTopology U ∧
      (∀ j, C j ⊆ U) ∧ ∀ g ∈ S, g • (U : Set X) = U := by
  obtain ⟨U, hUc, hUsc, hCU, hUinv⟩ :=
    exists_smul_invariant_opens_secondCountable (H := H) K hK hKmono C hC
  have hinv : ∀ g ∈ S, ∀ x ∈ U, g • x ∈ U := fun g hg => hUinv g (hS ▸ hg)
  refine ⟨U, hUc, hUsc, hCU, fun g hg => Subset.antisymm ?_ ?_⟩
  · exact smul_set_subset_iff.2 fun x hx => hinv g hg x hx
  · exact fun x hx => ⟨g⁻¹ • x, hinv g⁻¹ (inv_mem hg) x hx, smul_inv_smul g x⟩

end Exhaustion

section Restriction

variable {G X : Type*} [Monoid G] [TopologicalSpace X] [MulAction G X] (U : Opens X)
  (hU : ∀ g : G, ∀ x ∈ U, g • x ∈ U)

/-- The restriction of an action to an open set that every element maps into itself. -/
@[instance_reducible, to_additive
  /-- The restriction of an additive action to an open set that every element maps into itself. -/]
def invariantMulAction : MulAction G U where
  smul g x := ⟨g • x.1, hU g x.1 x.2⟩
  one_smul x := Subtype.ext (one_smul G x.1)
  mul_smul g h x := Subtype.ext (mul_smul g h x.1)

/-- The restricted action is the ambient action on underlying points. -/
@[to_additive /-- The restricted action is the ambient action on underlying points. -/]
theorem coe_smul_invariantMulAction (g : G) (x : U) :
    letI := invariantMulAction U hU
    ((g • x : U) : X) = g • (x : X) :=
  rfl

/-- The restriction of a continuous action to an invariant open set is continuous. -/
@[to_additive
  /-- The restriction of a continuous additive action to an invariant open set is continuous. -/]
theorem continuousSMul_invariantMulAction [TopologicalSpace G] [ContinuousSMul G X] :
    letI := invariantMulAction U hU
    ContinuousSMul G U :=
  letI := invariantMulAction U hU
  ⟨(continuous_fst.smul (continuous_subtype_val.comp continuous_snd)).subtype_mk _⟩

/-- The restriction of an action to an invariant open set is faithful if any two distinct elements
already act differently on some point of the set. -/
@[to_additive
  /-- The restriction of an additive action to an invariant open set is faithful if any two
  distinct elements already act differently on some point of the set. -/]
theorem faithfulSMul_invariantMulAction (h : ∀ g₁ g₂ : G, (∀ x ∈ U, g₁ • x = g₂ • x) → g₁ = g₂) :
    letI := invariantMulAction U hU
    FaithfulSMul G U :=
  letI := invariantMulAction U hU
  ⟨fun hg => h _ _ fun x hx => congrArg Subtype.val (hg ⟨x, hx⟩)⟩

end Restriction

end HilbertSmith
