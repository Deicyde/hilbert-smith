import Mathlib
import HilbertSmithPaper.Proofs.FaithfulHausdorff
import HilbertSmithPaper.LocalData.Subgroups.SmallDisplacement
import HilbertSmithPaper.Inputs.Newman.NewmanSmallOrbits
import HilbertSmithPaper.Inputs.Newman.NewmanOpenSet
import HilbertSmithPaper.Inputs.CompactGroups.ZpInTorsionFree
import HilbertSmithPaper.Proofs.PadicExclusion

/-!
# A faithfully acting group has no small subgroups

A locally compact topological group acting jointly continuously and faithfully on a connected
`n`-manifold (Hausdorff, charted on `ℝⁿ`) has a neighbourhood of `1` containing no subgroup other
than `⊥`. No countability is assumed on `M` or `G`, and no separation on `G`. `n` and `M` are
explicit, since the conclusion mentions only `G`.

The proof follows the article: `G` is Hausdorff; a chart composed with a translation and a dilation
gives `e` whose target contains the closed unit ball, `C = e⁻¹(B̄)` is compact and `δ` comes from
Newman's theorem on small orbits; small displacement gives `V ∋ 1` and local compactness a compact
`W ⊆ V`. For a subgroup `H ⊆ W`, its closure `K ⊆ W` is a compact Hausdorff group. An element of
prime order in `K` would fix `e⁻¹(B)` (small orbits), hence act trivially (fixing an open set),
against faithfulness; so `K` is torsion-free, and if `K ≠ 1` the embedding theorem gives a
continuous injective `ℤ_[p] → K`, whose restricted action contradicts `p`-adic exclusion.
-/

open scoped Topology
open Metric

namespace HSP

universe u v

/-- **No small subgroups.** A locally compact topological group acting jointly continuously and
faithfully on a connected `n`-manifold has a neighbourhood of `1` containing no subgroup other
than the trivial one. -/
theorem noSmallSubgroups (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M]
    [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (G : Type v) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [MulAction G M]
    [ContinuousSMul G M] [FaithfulSMul G M] :
    ∃ U ∈ 𝓝 (1 : G), ∀ H : Subgroup G, (H : Set G) ⊆ U → H = ⊥ := by
  classical
  -- step 1: `G` is Hausdorff
  have : T2Space G := t2Space_of_faithfulSMul (X := M)
  -- step 2: a chart whose target contains the closed unit ball
  obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
  set c := chartAt (EuclideanSpace ℝ (Fin n)) x₀
  have hx₀ : x₀ ∈ c.source := mem_chart_source _ x₀
  obtain ⟨r₀, hr₀, hr₀t⟩ := Metric.isOpen_iff.1 c.open_target (c x₀) (c.map_source hx₀)
  set r := r₀ / 2 with hr_def
  have hr : 0 < r := by positivity
  let aff : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n) :=
    (Homeomorph.smulOfNeZero r hr.ne').trans (Homeomorph.addLeft (c x₀))
  have haff : ∀ z, aff z = c x₀ + r • z := fun _ => rfl
  set e := c.transHomeomorph aff.symm with he_def
  have het : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ e.target := by
    intro z hz
    change aff.symm.symm z ∈ c.target
    rw [Homeomorph.symm_symm, haff]
    apply hr₀t
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    rw [mem_closedBall, dist_zero_right] at hz
    calc r * ‖z‖ ≤ r * 1 := mul_le_mul_of_nonneg_left hz hr.le
      _ < r₀ := by rw [hr_def]; linarith
  set C := e.symm '' closedBall (0 : EuclideanSpace ℝ (Fin n)) 1
  have hCc : IsCompact C :=
    (isCompact_closedBall _ _).image_of_continuousOn (e.continuousOn_symm.mono het)
  have hCs : C ⊆ e.source := by
    rintro _ ⟨z, hz, rfl⟩
    exact e.map_target (het hz)
  obtain ⟨δ, hδ, hNewman⟩ := newman_small_orbits e het
  -- step 3: small displacement and a compact neighbourhood
  obtain ⟨V, hV, hVd⟩ := exists_nhds_one_small_displacement (G := G) e hCc hCs hδ
  obtain ⟨W, hW, hWV, hWc⟩ := local_compact_nhds hV
  refine ⟨W, hW, fun H hH => ?_⟩
  -- step 4: the closure of `H`
  set K := H.topologicalClosure
  have hKW : (K : Set G) ⊆ W := by
    rw [Subgroup.topologicalClosure_coe]
    exact closure_minimal hH hWc.isClosed
  have hKc : IsCompact (K : Set G) := hWc.of_isClosed_subset H.isClosed_topologicalClosure hKW
  -- step 5: no element of finite order
  have htf : ∀ g ∈ K, IsOfFinOrder g → g = 1 := by
    intro g hgK hg
    by_contra hg1
    have hm0 : orderOf g ≠ 0 := hg.orderOf_pos.ne'
    have hm1 : orderOf g ≠ 1 := fun h => hg1 (orderOf_eq_one_iff.1 h)
    obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd hm1
    set h := g ^ (orderOf g / q)
    have hoh : orderOf h = q := orderOf_pow_orderOf_div hm0 hqm
    have hhK : ∀ k : ℕ, h ^ k ∈ K := fun k => K.pow_mem (K.pow_mem hgK _) k
    let f : M ≃ₜ M := Homeomorph.smul h
    have hiter : ∀ k : ℕ, ∀ x, (⇑f)^[k] x = h ^ k • x := fun k x => by
      change (fun y => h • y)^[k] x = _
      rw [smul_iterate]
    have hper : ∀ x, (⇑f)^[q] x = x := fun x => by
      rw [hiter, ← hoh, pow_orderOf_eq_one, one_smul]
    have hsmall : ∀ k : ℕ, ∀ x ∈ e.symm '' closedBall 0 1,
        (⇑f)^[k] x ∈ e.source ∧ dist (e ((⇑f)^[k] x)) (e x) < δ := fun k x hx => by
      rw [hiter]
      exact hVd _ (hWV (hKW (hhK k))) x hx
    have hfix := hNewman q hq f hper hsmall
    have hbt : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ e.target :=
      ball_subset_closedBall.trans het
    have hUo : IsOpen (e.symm '' ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
      rw [e.symm_image_eq_source_inter_preimage hbt]
      exact e.isOpen_inter_preimage isOpen_ball
    have hid := newman_open_set (n := n) f q hq.one_lt.le (funext hper) _ hUo
      ⟨_, 0, mem_ball_self one_pos, rfl⟩ hfix
    have h1 : h = 1 := eq_of_smul_eq_smul (α := M) fun x => by
      rw [one_smul]
      exact congrFun hid x
    rw [h1, orderOf_one] at hoh
    exact hq.one_lt.ne hoh
  -- step 6: `K` is trivial
  have hK : K = ⊥ := by
    by_contra hK0
    have : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).2 hK0
    have : CompactSpace K := isCompact_iff_compactSpace.1 hKc
    obtain ⟨p, hp, φ, hφc, hφi⟩ := exists_padic_embedding K fun g hg =>
      Subtype.ext (htf g g.2 (K.subtype.isOfFinOrder hg))
    let act : AddAction ℤ_[p] M :=
      { vadd := fun a x => ((φ (Multiplicative.ofAdd a) : K) : G) • x
        zero_vadd := fun x => by
          change ((φ (Multiplicative.ofAdd 0) : K) : G) • x = x
          rw [ofAdd_zero, map_one, Subgroup.coe_one, one_smul]
        add_vadd := fun a b x => by
          change ((φ (Multiplicative.ofAdd (a + b)) : K) : G) • x =
            ((φ (Multiplicative.ofAdd a) : K) : G) • ((φ (Multiplicative.ofAdd b) : K) : G) • x
          rw [ofAdd_add, map_mul, Subgroup.coe_mul, mul_smul] }
    have hcont : @ContinuousVAdd ℤ_[p] M act.toVAdd _ _ := by
      refine @ContinuousVAdd.mk ℤ_[p] M act.toVAdd _ _ ?_
      change Continuous fun q : ℤ_[p] × M => ((φ (Multiplicative.ofAdd q.1) : K) : G) • q.2
      exact ((continuous_subtype_val.comp (hφc.comp
        (continuous_ofAdd.comp continuous_fst))).smul continuous_snd)
    have hfaith : @FaithfulVAdd ℤ_[p] M act.toVAdd := by
      refine @FaithfulVAdd.mk ℤ_[p] M act.toVAdd fun {a₁ a₂} h12 => ?_
      have hG : ((φ (Multiplicative.ofAdd a₁) : K) : G) = ((φ (Multiplicative.ofAdd a₂) : K) : G) :=
        eq_of_smul_eq_smul (α := M) h12
      exact Multiplicative.ofAdd.injective (hφi (Subtype.ext hG))
    exact @padicExclusion n M _ _ _ _ p hp act hcont hfaith
  -- conclusion
  rw [eq_bot_iff]
  intro g hg
  have : g ∈ K := H.le_topologicalClosure hg
  rwa [hK] at this

end HSP
