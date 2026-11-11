import Mathlib
import HilbertSmithPaper.LocalData.Chart.LocalDatum
import HilbertSmithPaper.LocalData.Subgroups.GoodPoint
import HilbertSmithPaper.LocalData.Subgroups.SmallDisplacement
import HilbertSmithPaper.LocalData.Subgroups.PadicSubgroupsBasis
import HilbertSmithPaper.LocalData.Subgroups.FixedSetsClosed

/-!
# A local datum from a faithful action

A jointly continuous faithful action of `ℤ_[p]` on a connected `n`-manifold `M` (encoded as in the
good-point module) and `0 < D ≤ 1/64` give some `ρplus ∈ (0, 1/4)` and a local datum with constants
`(D, ρplus)` in dimension `n`.

The proof follows the article. With `e` the chart at a good point `x₀`, `z₀ = e x₀` and `s > 0` with
`B̄(z₀, 4s)` in the target: `C = e⁻¹(B̄(z₀, 3s))` is compact; small displacement and the basis
property give `j` with `|e(a +ᵥ m) - e m| < s D / 2` for `a ∈ H_j`, `m ∈ C`; a point `y₁` with
`|e y₁ - z₀| < s` outside `Fix_j` and a radius `r` with no point of `e⁻¹(B(e y₁, r))` in `Fix_j`
give `ρplus = min (r / 2s) (1/8)`. With `c = e y₁` and `φ = s⁻¹ (e - c)`, the open `H_j`-invariant
`Ω_M = ⋃_{b ∈ H_j} b +ᵥ e⁻¹(B(c, 2s))` is carried by `φ` homeomorphically onto `Ω ⊇ B(0, 2)`, and
`a ⋆ x = φ (p^j a +ᵥ φ⁻¹ x)` is the action.
-/

open Topology Metric

namespace HSP

/-- A faithful jointly continuous action of `ℤ_[p]` on a connected `n`-manifold gives a local datum
with constants `(D, ρplus)` for every `0 < D ≤ 1/64` and some `ρplus ∈ (0, 1/4)`. -/
theorem exists_localDatum {p : ℕ} [Fact p.Prime] {n : ℕ} {M : Type*} [TopologicalSpace M]
    [T2Space M] [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [AddAction ℤ_[p] M] [ContinuousVAdd ℤ_[p] M] [FaithfulVAdd ℤ_[p] M]
    {D : ℝ} (hD : 0 < D) (hD' : D ≤ 1 / 64) :
    ∃ ρplus : ℝ, 0 < ρplus ∧ ρplus < 1 / 4 ∧ Nonempty (LocalDatum p n D ρplus) := by
  classical
  -- step 1: a good point
  obtain ⟨x₀, hx₀⟩ := exists_good_point (p := p) (n := n) (M := M)
  -- step 2: the chart and the compact set
  set e := chartAt (EuclideanSpace ℝ (Fin n)) x₀ with he
  have hx₀s : x₀ ∈ e.source := mem_chart_source _ x₀
  obtain ⟨r₀, hr₀, hr₀t⟩ := Metric.isOpen_iff.1 e.open_target (e x₀) (e.map_source hx₀s)
  set s := r₀ / 5 with hs_def
  have hs : 0 < s := by positivity
  have h3t : closedBall (e x₀) (3 * s) ⊆ e.target :=
    (closedBall_subset_ball (by rw [hs_def]; linarith)).trans hr₀t
  set C := e.symm '' closedBall (e x₀) (3 * s)
  have hCc : IsCompact C :=
    (isCompact_closedBall _ _).image_of_continuousOn (e.continuousOn_symm.mono h3t)
  have hCs : C ⊆ e.source := by
    rintro _ ⟨z, hz, rfl⟩
    exact e.map_target (h3t hz)
  -- step 3: small displacement
  obtain ⟨V, hV, hVd⟩ := exists_nhds_zero_small_displacement (G := ℤ_[p]) e hCc hCs
    (half_pos (mul_pos hs hD))
  obtain ⟨j, hj⟩ := (padicSubgroup_basis p).2.2 V hV
  -- step 4: a nearby point outside `Fix_j` and the radius
  have hW : e.source ∩ e ⁻¹' ball (e x₀) s ∈ 𝓝 x₀ :=
    (e.isOpen_inter_preimage isOpen_ball).mem_nhds ⟨hx₀s, mem_ball_self hs⟩
  obtain ⟨y₁, ⟨hy₁s, hy₁b⟩, hy₁⟩ : ∃ y ∈ e.source ∩ e ⁻¹' ball (e x₀) s, y ∉ fixSet p M j := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    exact hx₀ j (Filter.mem_of_superset hW fun y hy => hcon y hy)
  set c := e y₁ with hc
  have hcz : dist c (e x₀) < s := hy₁b
  have hFo : IsOpen (e.target ∩ e.symm ⁻¹' (fixSet p M j)ᶜ) :=
    e.isOpen_inter_preimage_symm (isClosed_fixSet j).isOpen_compl
  obtain ⟨r, hr, hrF⟩ := Metric.isOpen_iff.1 hFo c
    ⟨e.map_source hy₁s, by simpa [c, e.left_inv hy₁s] using hy₁⟩
  set ρplus := min (r / (2 * s)) (1 / 8) with hρ
  have hρpos : 0 < ρplus := lt_min (by positivity) (by norm_num)
  have hρs : s * ρplus < r := by
    have : ρplus ≤ r / (2 * s) := min_le_left _ _
    calc s * ρplus ≤ s * (r / (2 * s)) := mul_le_mul_of_nonneg_left this hs.le
      _ = r / 2 := by field_simp
      _ < r := half_lt_self hr
  -- step 5: the set `Ω_M`
  set S : Set M := e.source ∩ e ⁻¹' ball c (2 * s) with hS
  have hSo : IsOpen S := e.isOpen_inter_preimage isOpen_ball
  have hSC : S ⊆ C := by
    rintro m ⟨hms, hmb⟩
    refine ⟨e m, ?_, e.left_inv hms⟩
    rw [mem_closedBall]
    have : dist (e m) c < 2 * s := hmb
    linarith [dist_triangle (e m) c (e x₀)]
  set Hj : Set ℤ_[p] := (padicSubgroup p j : Set ℤ_[p])
  set ΩM : Set M := ⋃ b ∈ Hj, (fun y => b +ᵥ y) '' S with hΩM
  have hΩMo : IsOpen ΩM := isOpen_biUnion fun b _ => isOpenMap_vadd b S hSo
  have hΩM_mem : ∀ y ∈ ΩM, ∃ b ∈ Hj, ∃ m ∈ S, b +ᵥ m = y := by
    intro y hy
    obtain ⟨b, hb, hy'⟩ := Set.mem_iUnion₂.1 hy
    obtain ⟨m, hm, rfl⟩ := hy'
    exact ⟨b, hb, m, hm, rfl⟩
  have hΩM_intro : ∀ b ∈ Hj, ∀ m ∈ S, b +ᵥ m ∈ ΩM := fun b hb m hm =>
    Set.mem_iUnion₂.2 ⟨b, hb, m, hm, rfl⟩
  have hclose : ∀ b ∈ Hj, ∀ m ∈ S, b +ᵥ m ∈ e.source ∧ dist (e (b +ᵥ m)) (e m) < s * D / 2 :=
    fun b hb m hm => hVd b (hj hb) m (hSC hm)
  have hΩMs : ΩM ⊆ e.source := by
    intro y hy
    obtain ⟨b, hb, m, hm, rfl⟩ := hΩM_mem y hy
    exact (hclose b hb m hm).1
  have hΩMinv : ∀ a ∈ Hj, ∀ y ∈ ΩM, a +ᵥ y ∈ ΩM := by
    intro a ha y hy
    obtain ⟨b, hb, m, hm, rfl⟩ := hΩM_mem y hy
    rw [vadd_vadd]
    exact hΩM_intro _ ((padicSubgroup p j).add_mem ha hb) m hm
  have hpj : ∀ a : ℤ_[p], (p : ℤ_[p]) ^ j * a ∈ Hj := fun a => dvd_mul_right _ _
  -- step 6: `Ω` and the homeomorphism `φ : Ω_M ≃ₜ Ω`
  set φ : M → EuclideanSpace ℝ (Fin n) := fun y => s⁻¹ • (e y - c) with hφ
  set Ω := φ '' ΩM with hΩ
  have hφinv : ∀ y ∈ e.source, e.symm (c + s • φ y) = y := by
    intro y hy
    simp only [φ, smul_smul, mul_inv_cancel₀ hs.ne', one_smul, add_sub_cancel]
    exact e.left_inv hy
  let h : ΩM ≃ₜ Ω :=
    { toFun := fun y => ⟨φ y, y, y.2, rfl⟩
      invFun := fun x => ⟨e.symm (c + s • (x : EuclideanSpace ℝ (Fin n))), by
        obtain ⟨y, hy, hyx⟩ := x.2
        rw [← hyx, hφinv y (hΩMs hy)]
        exact hy⟩
      left_inv := fun y => Subtype.ext (hφinv y (hΩMs y.2))
      right_inv := fun x => by
        apply Subtype.ext
        obtain ⟨y, hy, hyx⟩ := x.2
        change φ (e.symm (c + s • (x : EuclideanSpace ℝ (Fin n)))) = x
        rw [← hyx, hφinv y (hΩMs hy)]
      continuous_toFun := by
        refine Continuous.subtype_mk ?_ _
        have h1 : Continuous fun y : ΩM => e (y : M) :=
          e.continuousOn.comp_continuous continuous_subtype_val fun y => hΩMs y.2
        exact (h1.sub continuous_const).const_smul s⁻¹
      continuous_invFun := by
        refine Continuous.subtype_mk ?_ _
        refine e.continuousOn_symm.comp_continuous
          (continuous_const.add (continuous_subtype_val.const_smul s)) fun x => ?_
        obtain ⟨y, hy, hyx⟩ := x.2
        rw [← hyx]
        simp only [φ, smul_smul, mul_inv_cancel₀ hs.ne', one_smul, add_sub_cancel]
        exact e.map_source (hΩMs hy) }
  have hhval : ∀ y : ΩM, ((h y : Ω) : EuclideanSpace ℝ (Fin n)) = φ y := fun _ => rfl
  have hΩo : IsOpen Ω := by
    have himg : Ω = (fun z => s⁻¹ • (z - c)) '' (e '' ΩM) := by
      rw [Set.image_image]
    have haff : IsOpenMap fun z : EuclideanSpace ℝ (Fin n) => s⁻¹ • (z - c) := by
      have : (fun z : EuclideanSpace ℝ (Fin n) => s⁻¹ • (z - c)) =
          (fun z => s⁻¹ • z) ∘ (Homeomorph.addRight (-c)) := by
        funext z
        simp [sub_eq_add_neg]
      rw [this]
      exact (isOpenMap_smul₀ (inv_ne_zero hs.ne')).comp (Homeomorph.addRight (-c)).isOpenMap
    rw [himg]
    exact haff _ (e.isOpen_image_of_subset_source hΩMo hΩMs)
  -- step 7: the action
  let actM : ℤ_[p] → ΩM → ΩM := fun a y =>
    ⟨((p : ℤ_[p]) ^ j * a) +ᵥ (y : M), hΩMinv _ (hpj a) y y.2⟩
  have hactM0 : ∀ y, actM 0 y = y := fun y => Subtype.ext (by simp [actM])
  have hactMadd : ∀ a b y, actM (a + b) y = actM a (actM b y) := fun a b y =>
    Subtype.ext (by simp [actM, mul_add, add_vadd])
  let act : AddAction ℤ_[p] Ω :=
    { vadd := fun a x => h (actM a (h.symm x))
      zero_vadd := fun x => by
        change h (actM 0 (h.symm x)) = x
        rw [hactM0, h.apply_symm_apply]
      add_vadd := fun a b x => by
        change h (actM (a + b) (h.symm x)) = h (actM a (h.symm (h (actM b (h.symm x)))))
        rw [h.symm_apply_apply, hactMadd] }
  let _ : AddAction ℤ_[p] Ω := act
  have hcont : ContinuousVAdd ℤ_[p] Ω := by
    refine ⟨?_⟩
    change Continuous fun q : ℤ_[p] × Ω => h (actM q.1 (h.symm q.2))
    refine h.continuous.comp (Continuous.subtype_mk ?_ _)
    exact ((continuous_const.mul continuous_fst).vadd
      (continuous_subtype_val.comp (h.symm.continuous.comp continuous_snd)))
  refine ⟨ρplus, hρpos, (min_le_right _ _).trans_lt (by norm_num), ⟨?_⟩⟩
  exact
    { D_pos := hD
      D_le := hD'
      ρplus_pos := hρpos
      ρplus_lt := (min_le_right _ _).trans_lt (by norm_num)
      Ω := Ω
      isOpen_Ω := hΩo
      act := act
      continuousVAdd := hcont
      ball_subset := by
        intro z hz
        rw [mem_ball, dist_zero_right] at hz
        set w := c + s • z
        have hwc : dist w c < 2 * s := by
          rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
          nlinarith
        have hwt : w ∈ e.target := hr₀t (by
          rw [mem_ball]
          linarith [dist_triangle w c (e x₀)])
        have hm : e.symm w ∈ S := ⟨e.map_target hwt, by
          change e (e.symm w) ∈ ball c (2 * s)
          rw [e.right_inv hwt]
          exact hwc⟩
        refine ⟨e.symm w, ?_, ?_⟩
        · simpa using hΩM_intro 0 (padicSubgroup p j).zero_mem _ hm
        · simp only [φ, e.right_inv hwt, w, add_sub_cancel_left, smul_smul,
            inv_mul_cancel₀ hs.ne', one_smul]
      dist_vadd_le := by
        intro a x
        set y := h.symm x
        have hx : x = h y := (h.apply_symm_apply x).symm
        change dist ((h (actM a (h.symm x)) : Ω) : EuclideanSpace ℝ (Fin n)) (x : Ω) ≤ D
        rw [hx, h.symm_apply_apply, hhval, hhval]
        obtain ⟨b, hb, m, hm, hbm⟩ := hΩM_mem y y.2
        have h1 := (hclose b hb m hm).2
        have h2 := (hclose _ ((padicSubgroup p j).add_mem (hpj a) hb) m hm).2
        have hya : ((actM a y : ΩM) : M) = ((p : ℤ_[p]) ^ j * a + b) +ᵥ m := by
          change ((p : ℤ_[p]) ^ j * a) +ᵥ (y : M) = _
          rw [← hbm, vadd_vadd]
        simp only [φ]
        rw [dist_eq_norm, ← smul_sub, sub_sub_sub_cancel_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.2 hs), ← dist_eq_norm, hya, ← hbm]
        have h3 := dist_triangle (e (((p : ℤ_[p]) ^ j * a + b) +ᵥ m)) (e m) (e (b +ᵥ m))
        rw [dist_comm (e m)] at h3
        rw [inv_mul_le_iff₀ hs]
        linarith
      exists_moved := by
        intro x hx
        set y := h.symm x
        have hxy : (x : EuclideanSpace ℝ (Fin n)) = φ y := by
          rw [← hhval, h.apply_symm_apply]
        have hey : e y = c + s • (x : EuclideanSpace ℝ (Fin n)) := by
          rw [hxy]
          simp only [φ, smul_smul, mul_inv_cancel₀ hs.ne', one_smul, add_sub_cancel]
        have hyF : (y : M) ∉ fixSet p M j := by
          have hmem : e y ∈ ball c r := by
            rw [mem_ball, hey, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
              abs_of_pos hs]
            calc s * ‖(x : EuclideanSpace ℝ (Fin n))‖ ≤ s * ρplus :=
                  mul_le_mul_of_nonneg_left hx hs.le
              _ < r := hρs
          have := (hrF hmem).2
          simpa [e.left_inv (hΩMs y.2)] using this
        simp only [fixSet, Set.mem_ofPred_eq, not_forall] at hyF
        obtain ⟨a', ha', hne⟩ := hyF
        obtain ⟨a, rfl⟩ := ha'
        refine ⟨a, fun heq => hne ?_⟩
        have heq' : h (actM a y) = h y := by
          rw [h.apply_symm_apply]
          exact heq
        have := congrArg Subtype.val (h.injective heq')
        exact this }

end HSP
