import HSFormal.Inputs.GY.NSSIsLie
import HSFormal.Inputs.Lemma7
import HSFormal.MontgomeryPrime
import HSFormal.Newman.Newman
import HSFormal.Reduction
import HSFormal.Universe
import HSFormal.WeakInputs
import HSGeneral.Interior
import HSGeneral.Padic
import HilbertSmith.Statements
import HilbertSmith.Topology.InvariantOpens
import HilbertSmith.Topology.KernelQuotient

/-!
# The Hilbert–Smith theorem without second countability

HS_proof proves the Hilbert–Smith conjecture for second-countable groups acting on
second-countable manifolds. This file removes both assumptions, and the Hausdorff assumption on
the group, for groups and manifolds in `Type` only
(`HilbertSmith.Statements.HilbertSmithNoSC.{0, 0}`). The p-adic exclusion is a visible hypothesis
of `HSGeneral.hilbertSmithNoSC_of_padicExclusion`.

Formal Conjectures' `Hilbert5.hilbert_smith_conjecture`, which allows any universe and asks for a
real-analytic Lie group structure, is not proved here.

## Main results

* `HSGeneral.eq_bot_of_isCompact_of_fixes_open`: a compact subgroup that fixes a nonempty open set
  pointwise is trivial.
* `HSGeneral.exists_nhds_subgroup_fixes_open`: every subgroup inside some identity neighbourhood
  fixes a fixed nonempty open set pointwise.
* `HSGeneral.noSmallSubgroups_of_faithfulSMul`: hence the group has no small subgroups.
* `HSGeneral.isLieGroup_of_noSmallSubgroups`: the Gleason–Yamabe theorem without second
  countability.
* `HSGeneral.hilbertSmithNoSC_of_padicExclusion`, `HSGeneral.hilbertSmithNoSC`: the Hilbert–Smith
  theorem without countability, and `HSGeneral.hilbertSmithWithBoundary_noSC` for manifolds with
  boundary.

## Proof

The route is neither the HS paper's nor OpenAI's. The paper's proof of Corollary 1.2 uses the
reduction of compact groups to `ℤ_[p]` from [Pa19], Newman's theorem from [Pa19] and the
Gleason–Yamabe structure theorem; HS_proof proves the last of these only in the form "no small
subgroups implies Lie", which is all that is used here.

1. A compact identity neighbourhood `W` lies in an open subgroup `G₀` exhausted by compact sets.
   Some connected, second-countable open set `V₀` is `G₀`-invariant
   (`HilbertSmith.exists_subgroup_invariant_opens_secondCountable`).
2. The quotient `Q` of `G₀` by the kernel of its action on `V₀` is Hausdorff, locally compact and
   second countable, and acts faithfully on `V₀`, so it has no small subgroups
   (`HSFormal.noSmallSubgroups_of_metric'`). Pulled back to `G`, this gives an identity
   neighbourhood `O ⊆ W` whose subgroups fix `V₀` pointwise.
3. For a subgroup `S ⊆ O`, its closure `T` is compact and fixes `V₀` pointwise. The same
   construction applied to `T` gives a compact, second-countable quotient of `T` that acts
   faithfully on a second-countable manifold and is torsion-free by Newman's theorem. If `T` were
   nontrivial, the quotient would contain `ℤ_[p]` ([Tao11, Lemma 7]), contradicting the p-adic
   exclusion. So `T = ⊥`, and `G` has no small subgroups.
4. The Gleason–Yamabe theorem, which HS_proof proves without second countability, concludes.

## Declarations used from HS_proof

Headline theorem and statements:
* `HSFormal.padicExclusion` (p-adic exclusion, used only in `HSGeneral.hilbertSmithNoSC`), and the
  definitions `HSFormal.PadicExclusion`, `HSFormal.NoSmallSubgroups` and `HSFormal.IsLieGroup`.

Proved inputs (HS_proof's proofs of published results it states as `Prop`s):
* `HSFormal.Lemma7.compactTorsionFreeContainsPadic` ([Tao11, Lemma 7]);
* `HSFormal.Newman.newmanPrimeOrder` (Newman's theorem for prime order).

Internal lemmas:
* `HSFormal.noSmallSubgroups_of_metric'` (no small subgroups, for second-countable groups and
  manifolds);
* `HSFormal.eq_of_iterate_eq_of_eqOn_open` (Newman's second theorem for periodic maps);
* `HSFormal.false_of_padic_hom` (an embedded `ℤ_[p]` contradicts p-adic exclusion);
* the steps of HS_proof's Gleason–Yamabe proof: `HSFormal.GY.nonempty_weakGleasonNorm`,
  `HSFormal.GY.WeakGleasonNorm.nonempty_gleasonNorm`,
  `HSFormal.GY.GleasonNorm.exists_localExpStructure`, `HSFormal.GY.LocalExpStructure.contDiffMu`
  and `HSFormal.GY.LocalExpStructure.isLieGroup`;
* through `HSGeneral.of_faithfulSMul_topInterior`, HS_proof's topological interior of a manifold
  with boundary (see `HSGeneral/Interior.lean`).

## References

* [Pa19] J. Pardon, *Totally disconnected groups (not) acting on two-manifolds*, in Breadth in
  Contemporary Topology, Proc. Sympos. Pure Math. 102 (2019), 187–193.
* [Tao11] T. Tao, *The Hilbert–Smith conjecture*, blog post, 13 August 2011,
  https://terrytao.wordpress.com/2011/08/13/the-hilbert-smith-conjecture/
* The HS paper: HS_proof's `HSproof.tex`, Corollary 1.2 (Hilbert–Smith).
-/

open Set Topology TopologicalSpace Pointwise

namespace HSGeneral

section Group

variable {n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [ConnectedSpace M]
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MulAction G M] [ContinuousSMul G M] [FaithfulSMul G M]

include n M

/-- **A compact subgroup fixing a nonempty open set pointwise is trivial.** Given the p-adic
exclusion, a compact subgroup `K` of a group acting continuously and faithfully on a connected
manifold, all of whose elements fix every point of a nonempty open set `U`, is trivial. -/
theorem eq_bot_of_isCompact_of_fixes_open (hP : HSFormal.PadicExclusion) [T2Space G]
    (K : Subgroup G) (hK : IsCompact (K : Set G)) {U : Set M} (hU : IsOpen U) (hne : U.Nonempty)
    (hfix : ∀ g ∈ K, ∀ x ∈ U, g • x = x) : K = ⊥ := by
  by_contra hKbot
  obtain ⟨⟨g, hg⟩, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hKbot
  -- Some point `y` is moved by `g ≠ 1`.
  obtain ⟨y, hy⟩ : ∃ y : M, g • y ≠ y := by
    by_contra! h
    exact hg1 (Subtype.ext (eq_of_smul_eq_smul (α := M) fun x => by simp [h x]))
  obtain ⟨x₀, hx₀⟩ := hne
  -- A `K`-invariant, connected, second-countable open set `V` containing `x₀` and `y`.
  obtain ⟨V, hVc, hVsc, hCV, hVinv⟩ :=
    HilbertSmith.exists_subgroup_invariant_opens_secondCountable (H := EuclideanSpace ℝ (Fin n))
      K (fun _ => K) (fun _ => hK) monotone_const (iUnion_const _).symm
      (fun _ => ({x₀, y} : Set M)) fun _ => isCompact_singleton.insert x₀
  have hinv : ∀ k : K, ∀ x ∈ V, k • x ∈ V := fun k x hx => by
    have := smul_mem_smul_set (a := (k : G)) hx
    rwa [hVinv k k.2] at this
  let := HilbertSmith.invariantMulAction V hinv
  have := HilbertSmith.continuousSMul_invariantMulAction V hinv
  have : ConnectedSpace V := isConnected_iff_connectedSpace.mp hVc
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have : LocallyCompactSpace V := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) V
  have : MetrizableSpace V := metrizableSpace_of_t3_secondCountable V
  -- The quotient `Q` of `K` by the kernel of its action on `V`: compact, Hausdorff, second
  -- countable, acting faithfully on `V`.
  let Q := K ⧸ HilbertSmith.actionKer K V
  have hx₀V : x₀ ∈ V := hCV 0 (mem_insert x₀ _)
  have hyV : y ∈ V := hCV 0 (mem_insert_of_mem x₀ rfl)
  -- `Q` is torsion-free: an element of finite order fixes the nonempty open set `U ∩ V`, so it
  -- is the identity on `V` by Newman's theorem.
  have htf : ∀ q : Q, IsOfFinOrder q → q = 1 := by
    intro q hq
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    let _ : MetricSpace V := metrizableSpaceMetric V
    have hid := HSFormal.eq_of_iterate_eq_of_eqOn_open HSFormal.Newman.newmanPrimeOrder (n := n)
      (hU.preimage continuous_subtype_val) (U := Subtype.val ⁻¹' U) ⟨⟨x₀, hx₀V⟩, hx₀⟩
      (continuous_const_smul (k : Q)) (fun v hv => Subtype.ext (hfix k k.2 v hv)) (orderOf (k : Q))
      hq.orderOf_pos fun v => by rw [smul_iterate, pow_orderOf_eq_one]; exact one_smul Q v
    exact eq_of_smul_eq_smul (α := V) fun v => by rw [hid v, one_smul]
  have hnt : Nontrivial Q := by
    refine ⟨⟨((⟨g, hg⟩ : K) : Q), 1, fun h => hy ?_⟩⟩
    have := congrArg (fun q : Q => ((q • (⟨y, hyV⟩ : V) : V) : M)) h
    rw [one_smul] at this
    exact this
  -- By [Tao11, Lemma 7], `Q` contains a copy of some `ℤ_[p]`, which acts faithfully on `V`.
  obtain ⟨p, _, embed, hembed, hinj⟩ := HSFormal.Lemma7.compactTorsionFreeContainsPadic Q hnt htf
  exact HSFormal.false_of_padic_hom hP (n := n) (M := V) embed hembed hinj

omit [FaithfulSMul G M] in
/-- **Small subgroups fix an open set.** Given the p-adic exclusion, for a locally compact group
acting continuously on a connected manifold, there are a nonempty open set `U` and
an identity neighbourhood `O` with compact closure such that every subgroup inside `O` fixes `U`
pointwise. -/
theorem exists_nhds_subgroup_fixes_open (hP : HSFormal.PadicExclusion) [T2Space G]
    [LocallyCompactSpace G] :
    ∃ U : Set M, IsOpen U ∧ U.Nonempty ∧ ∃ O ∈ 𝓝 (1 : G), IsCompact (closure O) ∧
      ∀ S : Subgroup G, (S : Set G) ⊆ O → ∀ g ∈ S, ∀ x ∈ U, g • x = x := by
  obtain ⟨W, hWc, hW1⟩ := exists_compact_mem_nhds (1 : G)
  obtain ⟨G₀, Kn, hG₀o, hWG₀, hKc, hKm, hG₀K⟩ :=
    HilbertSmith.exists_isOpen_subgroup_eq_iUnion_isCompact hWc hW1
  obtain ⟨x₀⟩ : Nonempty M := inferInstance
  -- A `G₀`-invariant, connected, second-countable open set `V`.
  obtain ⟨V, hVc, hVsc, hCV, hVinv⟩ :=
    HilbertSmith.exists_subgroup_invariant_opens_secondCountable (H := EuclideanSpace ℝ (Fin n))
      G₀ Kn hKc hKm hG₀K (fun _ => {x₀}) fun _ => isCompact_singleton
  have hinv : ∀ k : G₀, ∀ x ∈ V, k • x ∈ V := fun k x hx => by
    have := smul_mem_smul_set (a := (k : G)) hx
    rwa [hVinv k k.2] at this
  let := HilbertSmith.invariantMulAction V hinv
  have := HilbertSmith.continuousSMul_invariantMulAction V hinv
  have : ConnectedSpace V := isConnected_iff_connectedSpace.mp hVc
  have : LocallyCompactSpace G₀ := hG₀o.locallyCompactSpace
  have : SigmaCompactSpace G₀ :=
    isSigmaCompact_iff_sigmaCompactSpace.mp (hG₀K ▸ isSigmaCompact_iUnion_of_isCompact _ hKc)
  have : LocallyCompactSpace V := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) V
  have : MetrizableSpace V := metrizableSpace_of_t3_secondCountable V
  -- The quotient of `G₀` by the kernel of its action on `V` has no small subgroups.
  let N := HilbertSmith.actionKer G₀ V
  let _ : MetricSpace V := metrizableSpaceMetric V
  obtain ⟨W', hW', hW'S⟩ := HSFormal.noSmallSubgroups_of_metric' (n := n) (M := V) (G := G₀ ⧸ N)
    HSFormal.Lemma7.compactTorsionFreeContainsPadic HSFormal.Newman.newmanPrimeOrder hP
  -- Pull its NSS neighbourhood back to `G`, inside `W`.
  let φ : G₀ → G₀ ⧸ N := QuotientGroup.mk
  refine ⟨V, V.isOpen, ⟨x₀, hCV 0 rfl⟩, Subtype.val '' (φ ⁻¹' W') ∩ W, ?_, ?_, ?_⟩
  · exact Filter.inter_mem (hG₀o.isOpenMap_subtype_val.image_mem_nhds
      (continuous_quot_mk.continuousAt.preimage_mem_nhds hW')) hW1
  · exact hWc.of_isClosed_subset isClosed_closure (closure_minimal inter_subset_right hWc.isClosed)
  · intro S hS g hg x hx
    -- The image of `S ∩ G₀` in the quotient is a subgroup inside `W'`, hence trivial.
    have hbot := hW'S ((S.subgroupOf G₀).map (QuotientGroup.mk' N)) <| by
      rintro _ ⟨a, ha, rfl⟩
      obtain ⟨b, hb, hba⟩ := (hS ha).1
      rwa [Subtype.val_injective hba] at hb
    have hgG₀ : g ∈ G₀ := hWG₀ (hS hg).2
    have hgN : (⟨g, hgG₀⟩ : G₀) ∈ N := by
      rw [← QuotientGroup.eq_one_iff, ← Subgroup.mem_bot, ← hbot]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hg)
    exact congrArg Subtype.val ((HilbertSmith.mem_actionKer.1 hgN) ⟨x, hx⟩)

/-- **No small subgroups.** Given the p-adic exclusion, a locally compact group acting
continuously and faithfully on a connected manifold has no small subgroups. -/
theorem noSmallSubgroups_of_faithfulSMul (hP : HSFormal.PadicExclusion) [LocallyCompactSpace G] :
    HSFormal.NoSmallSubgroups G := by
  have := HilbertSmith.t2Space_of_faithfulSMul (Q := G) (X := M)
  obtain ⟨U, hU, hUne, O, hO, hOc, hOfix⟩ := exists_nhds_subgroup_fixes_open (n := n) (M := M)
    (G := G) hP
  refine ⟨O, hO, fun S hS => ?_⟩
  -- The closure of `S` lies in the compact set `closure O`, and it fixes `U` pointwise because
  -- each point's stabiliser is closed. So it is trivial, and so is `S`.
  have hclosure : (S.topologicalClosure : Set G) = closure S := S.topologicalClosure_coe
  have hbot : S.topologicalClosure = ⊥ := by
    refine eq_bot_of_isCompact_of_fixes_open (n := n) hP _ ?_ hU hUne fun g hg x hx => ?_
    · rw [hclosure]
      exact hOc.of_isClosed_subset isClosed_closure (closure_mono hS)
    · rw [← SetLike.mem_coe, hclosure] at hg
      refine closure_minimal (fun s hs => hOfix S hS s hs x hx) ?_ hg
      exact isClosed_eq (continuous_id.smul continuous_const) continuous_const
  exact le_bot_iff.1 (hbot ▸ S.le_topologicalClosure)

end Group

/-- **The Gleason–Yamabe theorem without second countability**: a locally compact Hausdorff group
with no small subgroups is a Lie group. HS_proof's `HSFormal.GY.nssIsLie` assumes second
countability but does not use it; this calls the steps of its proof directly: a weak Gleason
norm, then a Gleason norm, then a local exponential structure whose group law is smooth. -/
theorem isLieGroup_of_noSmallSubgroups {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    (hNSS : HSFormal.NoSmallSubgroups G) : HSFormal.IsLieGroup G :=
  (HSFormal.GY.nonempty_weakGleasonNorm hNSS).elim fun weakNorm =>
    weakNorm.nonempty_gleasonNorm.elim fun gleasonNorm =>
      gleasonNorm.exists_localExpStructure.elim fun _ hexp =>
        hexp.elim fun expStructure => expStructure.isLieGroup expStructure.contDiffMu

/-- **Hilbert–Smith without countability, from p-adic exclusion.** If no continuous action of
`ℤ_[p]` on a connected, Hausdorff, second-countable manifold is faithful, then every locally
compact group acting continuously and faithfully on a connected, Hausdorff manifold is a Lie
group, for groups and manifolds in `Type`. -/
theorem hilbertSmithNoSC_of_padicExclusion (hP : HSFormal.PadicExclusion) :
    HilbertSmith.Statements.HilbertSmithNoSC.{0, 0} := by
  intro n M _ _ _ _ G _ _ _ _ _ _ _
  have := HilbertSmith.t2Space_of_faithfulSMul (Q := G) (X := M)
  exact isLieGroup_of_noSmallSubgroups (noSmallSubgroups_of_faithfulSMul (n := n) (M := M) hP)

/-- **The Hilbert–Smith theorem without countability**, for groups and manifolds in `Type`: a
locally compact group acting continuously and faithfully on a connected, Hausdorff topological
manifold without boundary is a Lie group. Formal Conjectures' `Hilbert5.hilbert_smith_conjecture`
(any universe, real-analytic conclusion) is not proved here. -/
theorem hilbertSmithNoSC : HilbertSmith.Statements.HilbertSmithNoSC.{0, 0} :=
  hilbertSmithNoSC_of_padicExclusion HSFormal.padicExclusion

/-- **The Hilbert–Smith theorem for manifolds with boundary, without countability**, for groups
and manifolds in `Type`: a locally compact group acting continuously and faithfully on a
connected, Hausdorff topological manifold with boundary of dimension `n + 1` is a Lie group. It
follows from `HSGeneral.hilbertSmithNoSC` applied to the interior
(`HSGeneral.of_faithfulSMul_topInterior`). -/
theorem hilbertSmithWithBoundary_noSC {n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [ConnectedSpace M]
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MulAction G M] [ContinuousSMul G M] [FaithfulSMul G M] :
    HilbertSmith.Statements.IsLieGroup G :=
  of_faithfulSMul_topInterior (n := n) (X := M) (G := G) fun Y _ _ _ _ _ _ _ =>
    hilbertSmithNoSC (n + 1) Y G

end HSGeneral
