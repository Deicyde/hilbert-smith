import Mathlib
import HilbertSmithPaper.LocalData.Subgroups.GoodPoint
import HilbertSmithPaper.LocalData.Subgroups.SmallDisplacement
import HilbertSmithPaper.LocalData.Subgroups.PadicSubgroupsBasis
import HilbertSmithPaper.LocalData.Subgroups.ClosedSubgroups

/-!
# Reduction to one chart

A faithful jointly continuous action of `ℤ_[p]` on a connected `n`-manifold `M` (Hausdorff,
charted on `ℝⁿ`, no countability assumption) yields a nonempty connected open set `O ⊆ ℝⁿ` with a
faithful jointly continuous action of `ℤ_[p]`. "Nonempty connected" is `IsConnected O`; the
action on `O` is an `AddAction` on the subtype, existentially quantified.

The proof follows the article. Take a good point `x`, the chart `e` at `x` and the coordinate ball
`B = e⁻¹(B(e x, s))` with compact closure `e⁻¹(B̄(e x, s))` in the domain. Small displacement and
the basis property give `j` with `H_j B̄` in the domain and `H_j x ⊆ B`. The saturation
`O' = ⋃_{a ∈ H_j} a +ᵥ B` is open, `H_j`-invariant and connected. The kernel of the `H_j`-action on
`O'` is a closed subgroup; if it were nonzero it would be some `H_i` and fix the neighbourhood `O'`
of `x`, against the choice of `x`. The action `a ⋆ y = e (p^j a +ᵥ e⁻¹ y)` on `O = e(O')` is then
jointly continuous and faithful.
-/

open Topology Metric Pointwise

namespace HSP

/-- **Reduction to one chart.** A faithful jointly continuous action of `ℤ_[p]` on a connected
`n`-manifold gives a faithful jointly continuous action of `ℤ_[p]` on a nonempty connected open
subset of `ℝⁿ`. -/
theorem oneChart {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (p : ℕ) [Fact p.Prime] [AddAction ℤ_[p] M]
    [ContinuousVAdd ℤ_[p] M] [FaithfulVAdd ℤ_[p] M] :
    ∃ O : Set (EuclideanSpace ℝ (Fin n)), IsOpen O ∧ IsConnected O ∧
      ∃ (_ : AddAction ℤ_[p] O), ContinuousVAdd ℤ_[p] O ∧ FaithfulVAdd ℤ_[p] O := by
  classical
  -- step 1: a good point, a chart and a coordinate ball
  obtain ⟨x, hx⟩ := exists_good_point (p := p) (n := n) (M := M)
  set e := chartAt (EuclideanSpace ℝ (Fin n)) x with he
  have hxs : x ∈ e.source := mem_chart_source _ x
  obtain ⟨r₀, hr₀, hr₀t⟩ := Metric.isOpen_iff.1 e.open_target (e x) (e.map_source hxs)
  set s := r₀ / 2 with hs_def
  have hs : 0 < s := by positivity
  have hcbt : closedBall (e x) s ⊆ e.target :=
    (closedBall_subset_ball (by rw [hs_def]; linarith)).trans hr₀t
  have hbt : ball (e x) s ⊆ e.target := ball_subset_closedBall.trans hcbt
  set B := e.symm '' ball (e x) s with hB
  set C := e.symm '' closedBall (e x) s with hC
  have hCc : IsCompact C :=
    (isCompact_closedBall _ _).image_of_continuousOn (e.continuousOn_symm.mono hcbt)
  have hCs : C ⊆ e.source := by
    rintro _ ⟨z, hz, rfl⟩
    exact e.map_target (hcbt hz)
  have hBC : B ⊆ C := Set.image_mono ball_subset_closedBall
  have hBo : IsOpen B := by
    rw [hB, e.symm_image_eq_source_inter_preimage hbt]
    exact e.isOpen_inter_preimage isOpen_ball
  have hBc : IsPreconnected B :=
    (convex_ball (e x) s).isPreconnected.image _ (e.continuousOn_symm.mono hbt)
  have hxB : x ∈ B := ⟨e x, mem_ball_self hs, e.left_inv hxs⟩
  -- step 2: small displacement
  obtain ⟨V, hV, hVd⟩ := exists_nhds_zero_small_displacement (G := ℤ_[p]) e hCc hCs hs
  obtain ⟨j, hj⟩ := (padicSubgroup_basis p).2.2 V hV
  set Hj : Set ℤ_[p] := (padicSubgroup p j : Set ℤ_[p])
  have hxHB : ∀ a ∈ Hj, a +ᵥ x ∈ B := by
    intro a ha
    obtain ⟨hsrc, hd⟩ := hVd a (hj ha) x (hBC hxB)
    exact ⟨e (a +ᵥ x), hd, e.left_inv hsrc⟩
  -- step 3: the saturation
  set O' : Set M := ⋃ a ∈ Hj, a +ᵥ B with hO'
  have hO'o : IsOpen O' := isOpen_biUnion fun a _ => hBo.vadd a
  have hO'_mem : ∀ y ∈ O', ∃ a ∈ Hj, ∃ b ∈ B, a +ᵥ b = y := by
    intro y hy
    obtain ⟨a, ha, hy'⟩ := Set.mem_iUnion₂.1 hy
    obtain ⟨b, hb, rfl⟩ := Set.mem_vadd_set.1 hy'
    exact ⟨a, ha, b, hb, rfl⟩
  have hO'_intro : ∀ a ∈ Hj, ∀ b ∈ B, a +ᵥ b ∈ O' := fun a ha b hb =>
    Set.mem_iUnion₂.2 ⟨a, ha, Set.vadd_mem_vadd_set hb⟩
  have hxO' : x ∈ O' := by simpa using hO'_intro 0 (padicSubgroup p j).zero_mem x hxB
  have hO's : O' ⊆ e.source := by
    intro y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := hO'_mem y hy
    exact (hVd a (hj ha) b (hBC hb)).1
  have hO'inv : ∀ c ∈ Hj, ∀ y ∈ O', c +ᵥ y ∈ O' := by
    intro c hc y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := hO'_mem y hy
    rw [vadd_vadd]
    exact hO'_intro _ ((padicSubgroup p j).add_mem hc ha) b hb
  have hO'conn : IsConnected O' := by
    refine ⟨⟨x, hxO'⟩, ?_⟩
    have : O' = ⋃₀ ((fun a : ℤ_[p] => B ∪ (a +ᵥ B)) '' Hj) := by
      apply Set.Subset.antisymm
      · intro y hy
        obtain ⟨a, ha, b, hb, rfl⟩ := hO'_mem y hy
        exact ⟨_, ⟨a, ha, rfl⟩, Or.inr (Set.vadd_mem_vadd_set hb)⟩
      · rintro y ⟨_, ⟨a, ha, rfl⟩, hy | hy⟩
        · simpa using hO'_intro 0 (padicSubgroup p j).zero_mem y hy
        · obtain ⟨b, hb, rfl⟩ := Set.mem_vadd_set.1 hy
          exact hO'_intro a ha b hb
    rw [this]
    refine isPreconnected_sUnion x _ ?_ ?_
    · rintro _ ⟨a, -, rfl⟩
      exact Or.inl hxB
    · rintro _ ⟨a, ha, rfl⟩
      have haB : IsPreconnected (a +ᵥ B) := by
        rw [← Set.image_vadd]
        exact hBc.image _ (continuous_const_vadd a).continuousOn
      exact hBc.union (a +ᵥ x) (hxHB a ha) (Set.vadd_mem_vadd_set hxB) haB
  -- step 4: the kernel is zero
  have hker : ∀ b : ℤ_[p], (∀ y ∈ O', b +ᵥ y = y) → b = 0 := by
    intro b hb
    let K : AddSubgroup ℤ_[p] :=
      { carrier := {c | ∀ y ∈ O', c +ᵥ y = y}
        add_mem' := fun {c d} hc hd y hy => by
          change (c + d) +ᵥ y = y
          rw [← vadd_vadd, hd y hy, hc y hy]
        zero_mem' := fun y _ => zero_vadd _ y
        neg_mem' := fun {c} hc y hy => by
          change -c +ᵥ y = y
          conv_lhs => rw [← hc y hy]
          rw [neg_vadd_vadd] }
    have hKc : IsClosed (K : Set ℤ_[p]) := by
      have : (K : Set ℤ_[p]) = ⋂ y ∈ O', {c : ℤ_[p] | c +ᵥ y = y} := by
        ext c
        simp [K]
      rw [this]
      exact isClosed_biInter fun y _ => isClosed_eq (continuous_id.vadd continuous_const)
        continuous_const
    by_contra hb0
    have hK0 : K ≠ ⊥ := fun h => hb0 (by
      have : b ∈ K := hb
      rw [h] at this
      exact (AddSubgroup.mem_bot).1 this)
    obtain ⟨i, hi⟩ := closed_eq_padicSubgroup K hKc hK0
    refine hx i (Filter.mem_of_superset (hO'o.mem_nhds hxO') fun y hy a ha => ?_)
    have : a ∈ K := by rw [hi]; exact ha
    exact this y hy
  -- step 5: the action on `O = e(O')`
  set O := e '' O' with hO
  let h : O' ≃ₜ O := e.homeomorphOfImageSubsetSource hO's rfl
  have hhval : ∀ y : O', ((h y : O) : EuclideanSpace ℝ (Fin n)) = e y := fun _ => rfl
  have hpj : ∀ a : ℤ_[p], (p : ℤ_[p]) ^ j * a ∈ Hj := fun a => dvd_mul_right _ _
  let actM : ℤ_[p] → O' → O' := fun a y =>
    ⟨((p : ℤ_[p]) ^ j * a) +ᵥ (y : M), hO'inv _ (hpj a) y y.2⟩
  have hactM0 : ∀ y, actM 0 y = y := fun y => Subtype.ext (by simp [actM])
  have hactMadd : ∀ a b y, actM (a + b) y = actM a (actM b y) := fun a b y =>
    Subtype.ext (by simp [actM, mul_add, add_vadd])
  let act : AddAction ℤ_[p] O :=
    { vadd := fun a y => h (actM a (h.symm y))
      zero_vadd := fun y => by
        change h (actM 0 (h.symm y)) = y
        rw [hactM0, h.apply_symm_apply]
      add_vadd := fun a b y => by
        change h (actM (a + b) (h.symm y)) = h (actM a (h.symm (h (actM b (h.symm y)))))
        rw [h.symm_apply_apply, hactMadd] }
  refine ⟨O, e.isOpen_image_of_subset_source hO'o hO's,
    hO'conn.image e (e.continuousOn.mono hO's), act, ?_, ?_⟩
  · refine ⟨?_⟩
    change Continuous fun q : ℤ_[p] × O => h (actM q.1 (h.symm q.2))
    refine h.continuous.comp (Continuous.subtype_mk ?_ _)
    exact ((continuous_const.mul continuous_fst).vadd
      (continuous_subtype_val.comp (h.symm.continuous.comp continuous_snd)))
  · refine ⟨fun {a₁ a₂} heq => ?_⟩
    have hfix : ∀ y ∈ O', ((p : ℤ_[p]) ^ j * a₁) +ᵥ y = ((p : ℤ_[p]) ^ j * a₂) +ᵥ y := by
      intro y hy
      have h1 := heq (h ⟨y, hy⟩)
      change h (actM a₁ (h.symm (h ⟨y, hy⟩))) = h (actM a₂ (h.symm (h ⟨y, hy⟩))) at h1
      rw [h.symm_apply_apply] at h1
      exact congrArg Subtype.val (h.injective h1)
    have hb : ∀ y ∈ O', ((p : ℤ_[p]) ^ j * a₁ - (p : ℤ_[p]) ^ j * a₂) +ᵥ y = y := by
      intro y hy
      have hy' := hO'inv _ ((padicSubgroup p j).neg_mem (hpj a₂)) y hy
      rw [sub_eq_add_neg, ← vadd_vadd, hfix _ hy', vadd_vadd, add_neg_cancel, zero_vadd]
    have h0 := hker _ hb
    rw [← mul_sub, mul_eq_zero] at h0
    rcases h0 with h0 | h0
    · exact absurd h0 (pow_ne_zero j (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero))
    · exact sub_eq_zero.1 h0

end HSP
