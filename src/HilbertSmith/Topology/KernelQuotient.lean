import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.Metrizable.Urysohn

/-!
# Faithful actions, action kernels and second countability

A group acting continuously on a manifold that is not second countable can be replaced by its
quotient by the kernel of the action on an invariant second-countable open set. This file proves
the facts about such quotients that the Hilbert–Smith reduction needs. It imports Mathlib only.

## Main results

* `HilbertSmith.t2Space_of_faithfulSMul`: a topological group acting continuously and faithfully
  on a T₁ space is Hausdorff.
* `HilbertSmith.metrizableSpace_of_isCompact_of_faithfulSMul`: if a space acts continuously and
  faithfully on a separable metrizable space, its compact subsets are metrizable.
* `HilbertSmith.secondCountableTopology_of_faithfulSMul`: a weakly locally compact, σ-compact
  space acting continuously and faithfully on a second-countable metrizable space is second
  countable.
* `HilbertSmith.actionKer`: the kernel of an action, a closed normal subgroup. The quotient by it
  acts continuously and faithfully, and it is second countable when the group is locally compact
  and σ-compact and the space is second countable and metrizable
  (`HilbertSmith.secondCountableTopology_quotient_actionKer`), hence metrizable.
* `HilbertSmith.exists_isOpen_subgroup_eq_iUnion_isCompact`: in a topological group, a compact
  identity neighbourhood lies in an open subgroup that is the union of an increasing sequence of
  compact sets.

## Implementation notes

Second countability does not go through the Birkhoff–Kakutani theorem. A compact subset `K` of the
acting space maps into `X ^ D` for a countable dense `D ⊆ X`, by `q ↦ (q • d)_d`; faithfulness
makes this injective, so `K` is metrizable by `MetrizableSpace.of_countable_separating`, hence
second countable. Countably many interiors of compact neighbourhoods cover a σ-compact space, and
`secondCountableTopology_of_countable_cover` concludes.
-/

open Set Topology TopologicalSpace Pointwise

namespace HilbertSmith

section Faithful

variable {Q X : Type*} [TopologicalSpace Q] [TopologicalSpace X]

/-- A topological group acting continuously and faithfully on a T₁ space is Hausdorff: an element
in the closure of `1` maps each point into the closure of that point, which is the point itself. -/
@[to_additive
  /-- An additive topological group acting continuously and faithfully on a T₁ space is
  Hausdorff. -/]
theorem t2Space_of_faithfulSMul [Group Q] [IsTopologicalGroup Q] [T1Space X] [MulAction Q X]
    [ContinuousSMul Q X] [FaithfulSMul Q X] : T2Space Q := by
  have hclosed : IsClosed ({1} : Set Q) := by
    refine closure_subset_iff_isClosed.mp fun g hg => mem_singleton_iff.2 ?_
    refine eq_of_smul_eq_smul (α := X) fun x => ?_
    have hcont : Continuous fun h : Q => h • x := continuous_id.smul continuous_const
    have hx : g • x ∈ closure {x} := map_mem_closure (f := fun h : Q => h • x) hcont hg
      fun h hh => by simp [mem_singleton_iff.1 hh]
    rw [closure_singleton, mem_singleton_iff] at hx
    rw [hx, one_smul]
  have := IsTopologicalGroup.t1Space Q hclosed
  infer_instance

/-- If a space acts continuously and faithfully on a separable metrizable space, then each of its
compact subsets is metrizable. -/
@[to_additive
  /-- If a space acts additively, continuously and faithfully on a separable metrizable space,
  then each of its compact subsets is metrizable. -/]
theorem metrizableSpace_of_isCompact_of_faithfulSMul [SMul Q X] [ContinuousSMul Q X]
    [FaithfulSMul Q X] [SeparableSpace X] [MetrizableSpace X] {K : Set Q} (hK : IsCompact K) :
    MetrizableSpace K := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨D, hDc, hDd⟩ := exists_countable_dense X
  have : Encodable D := @Encodable.ofCountable _ hDc.to_subtype
  let := metrizableSpaceMetric X
  refine Metric.PiNatEmbed.TopologicalSpace.MetrizableSpace.of_countable_separating
    (fun (d : D) (q : K) => (q : Q) • (d : X)) (fun d => continuous_subtype_val.smul continuous_const) fun q₁ q₂ hne => ?_
  by_contra! h
  refine hne (Subtype.ext (eq_of_smul_eq_smul (α := X) fun x => ?_))
  exact congrFun ((continuous_const_smul _).ext_on hDd (continuous_const_smul _)
    fun d hd => h ⟨d, hd⟩) x

/-- A weakly locally compact, σ-compact space acting continuously and faithfully on a
second-countable metrizable space is second countable. -/
@[to_additive
  /-- A weakly locally compact, σ-compact space acting additively, continuously and faithfully on
  a second-countable metrizable space is second countable. -/]
theorem secondCountableTopology_of_faithfulSMul [WeaklyLocallyCompactSpace Q]
    [SigmaCompactSpace Q] [SMul Q X] [ContinuousSMul Q X] [FaithfulSMul Q X]
    [SecondCountableTopology X] [MetrizableSpace X] : SecondCountableTopology Q := by
  choose K hKc hKn using fun q : Q => exists_compact_mem_nhds q
  -- The interior of each compact neighbourhood `K q` is second countable, as `K q` is.
  have hsc : ∀ q, SecondCountableTopology (interior (K q)) := fun q => by
    have := metrizableSpace_of_isCompact_of_faithfulSMul (X := X) (hKc q)
    have : CompactSpace (K q) := isCompact_iff_compactSpace.mp (hKc q)
    exact (IsEmbedding.inclusion interior_subset).secondCountableTopology
  obtain ⟨s, hs, hsU⟩ := countable_cover_nhds_of_sigmaCompact fun q => interior_mem_nhds.2 (hKn q)
  have := hs.to_subtype
  exact secondCountableTopology_of_countable_cover (U := fun q : s => interior (K q))
    (fun _ => isOpen_interior) (by rwa [biUnion_eq_iUnion] at hsU)

end Faithful

section ActionKernel

variable (H X : Type*) [Group H] [MulAction H X]

/-- The kernel of an action: the elements acting as the identity. -/
def actionKer : Subgroup H := (MulAction.toPermHom H X).ker

variable {H X}

@[simp]
theorem mem_actionKer {g : H} : g ∈ actionKer H X ↔ ∀ x : X, g • x = x :=
  Equiv.ext_iff

instance : (actionKer H X).Normal := MonoidHom.normal_ker _

/-- The quotient by the kernel acts on the space. -/
instance : MulAction (H ⧸ actionKer H X) X :=
  MulAction.compHom X (QuotientGroup.kerLift (MulAction.toPermHom H X))

@[simp]
theorem mk_smul_actionKer (g : H) (x : X) : (g : H ⧸ actionKer H X) • x = g • x :=
  rfl

instance : FaithfulSMul (H ⧸ actionKer H X) X :=
  ⟨fun h => QuotientGroup.kerLift_injective _ (Equiv.ext h)⟩

variable [TopologicalSpace H] [TopologicalSpace X] [ContinuousSMul H X]

/-- The kernel of a continuous action on a Hausdorff space is closed. -/
instance [T2Space X] : IsClosed (actionKer H X : Set H) := by
  have : (actionKer H X : Set H) = ⋂ x : X, {g | g • x = x} := by
    ext g
    simp
  rw [this]
  exact isClosed_iInter fun x => isClosed_eq (continuous_id.smul continuous_const) continuous_const

instance [IsTopologicalGroup H] : ContinuousSMul (H ⧸ actionKer H X) X := by
  refine ⟨(QuotientGroup.isOpenQuotientMap_mk.prodMap IsOpenQuotientMap.id).continuous_comp_iff.1
    ?_⟩
  exact continuous_smul

/-- A quotient of a σ-compact group is σ-compact. -/
theorem sigmaCompactSpace_quotient [SigmaCompactSpace H] (N : Subgroup H) :
    SigmaCompactSpace (H ⧸ N) := by
  rw [← isSigmaCompact_univ_iff, ← image_univ_of_surjective QuotientGroup.mk_surjective]
  exact isSigmaCompact_univ.image continuous_quot_mk

/-- **Second countability of the quotient by the kernel.** If a locally compact, σ-compact
topological group acts continuously on a second-countable metrizable space, the quotient by the
kernel of the action is second countable. -/
instance secondCountableTopology_quotient_actionKer [IsTopologicalGroup H] [LocallyCompactSpace H]
    [SigmaCompactSpace H] [SecondCountableTopology X] [MetrizableSpace X] :
    SecondCountableTopology (H ⧸ actionKer H X) :=
  have := sigmaCompactSpace_quotient (actionKer H X)
  secondCountableTopology_of_faithfulSMul (X := X)

/-- Under the same hypotheses, the quotient by the kernel is metrizable. -/
theorem metrizableSpace_quotient_actionKer [IsTopologicalGroup H] [LocallyCompactSpace H]
    [SigmaCompactSpace H] [SecondCountableTopology X] [MetrizableSpace X] :
    MetrizableSpace (H ⧸ actionKer H X) :=
  metrizableSpace_of_t3_secondCountable _

end ActionKernel

section OpenSubgroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **An open σ-compact subgroup.** In a topological group, a compact identity neighbourhood `W`
lies in an open subgroup that is the union of an increasing sequence of compact sets, namely the
powers of `W ∪ W⁻¹`. -/
@[to_additive
  /-- **An open σ-compact subgroup.** In an additive topological group, a compact neighbourhood
  `W` of zero lies in an open subgroup that is the union of an increasing sequence of compact
  sets, namely the multiples of `W ∪ -W`. -/]
theorem exists_isOpen_subgroup_eq_iUnion_isCompact {W : Set G} (hW : IsCompact W)
    (h1 : W ∈ 𝓝 1) : ∃ (S : Subgroup G) (K : ℕ → Set G), IsOpen (S : Set G) ∧ W ⊆ S ∧
      (∀ j, IsCompact (K j)) ∧ Monotone K ∧ (S : Set G) = ⋃ j, K j := by
  set V := W ∪ W⁻¹
  have hV1 : (1 : G) ∈ V := .inl (mem_of_mem_nhds h1)
  have hVinv : ∀ j, ∀ g ∈ V ^ j, g⁻¹ ∈ V ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rintro _ ⟨a, ha, b, hb, rfl⟩
      rw [mul_inv_rev, pow_succ']
      refine mul_mem_mul ?_ (ih a ha)
      rcases hb with hb | hb
      · exact .inr (inv_mem_inv.2 hb)
      · exact .inl (mem_inv.1 hb)
  let S : Subgroup G :=
    { carrier := ⋃ j, V ^ j
      mul_mem' := by
        rintro _ _ ⟨_, ⟨i, rfl⟩, ha⟩ ⟨_, ⟨j, rfl⟩, hb⟩
        exact mem_iUnion.2 ⟨i + j, pow_add V i j ▸ mul_mem_mul ha hb⟩
      one_mem' := mem_iUnion.2 ⟨0, by simp⟩
      inv_mem' := by
        rintro _ ⟨_, ⟨j, rfl⟩, ha⟩
        exact mem_iUnion.2 ⟨j, hVinv j _ ha⟩ }
  have hWS : W ⊆ S := fun g hg => mem_iUnion.2 ⟨1, by rw [pow_one]; exact .inl hg⟩
  refine ⟨S, fun j => V ^ j, S.isOpen_of_mem_nhds (Filter.mem_of_superset h1 hWS), hWS, ?_,
    Set.pow_right_monotone hV1, rfl⟩
  have hVc : IsCompact V := hW.union hW.inv
  intro j
  induction j with
  | zero => simp
  | succ j ih => exact (pow_succ V j ▸ ih.mul hVc : IsCompact (V ^ (j + 1)))

end OpenSubgroup

/-- A test of the instances: the quotient of a compact group acting continuously on a
second-countable manifold, by the kernel of the action, is second countable and Hausdorff. -/
example {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] {K : Type*} [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [T2Space K] [MulAction K M] [ContinuousSMul K M] :
    SecondCountableTopology (K ⧸ actionKer K M) ∧ T2Space (K ⧸ actionKer K M) := by
  have := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  have := metrizableSpace_of_t3_secondCountable M
  exact ⟨inferInstance, inferInstance⟩

end HilbertSmith
