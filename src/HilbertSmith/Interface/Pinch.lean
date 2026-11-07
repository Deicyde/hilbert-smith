import HilbertSmith.Interface.Spaces

/-!
# Pinch maps

The proof of OpenAI's Lemma 5.3 (05:153-161) fixes a map `P : ℝ^d → S^d`, constant `ξ` outside
the unit ball and inducing an orientation-preserving homeomorphism `B̄^d/∂B^d → S^d`, and pinches
`P_{z,r}(w) = P((w − z)/r)`, `P_{z,r}(∞) = ξ`, on `W⁺` for closed balls `B̄(z, r) ⊆ W`. It then
uses that `P_{z,r} c` has degree one. This file chooses `P` so that no degree is needed.

* The **radial blow-up** `ρ_s(u) = (1 − s‖u‖)⁻¹ u`, and `∞` when `s‖u‖ ≥ 1`, maps the open ball of
  radius `1/s` homeomorphically onto `E` for `s > 0`, and is the inclusion for `s = 0`.
* The **pinch** `Ψ_{z,r,s} : E⁺ → E⁺` sends `∞` to `∞` and `v` to `ρ_s((v − z)/r)`. It depends
  continuously on `(z, r, s)` with `r > 0` and `s ≥ 0` (`continuous_pinchE`), and `Ψ_{0,1,0}` is the
  identity.
* The pinch on `W⁺` (`LocalAction.pinch z r`) is `Ψ_{z,r,1}` followed by `S^d ≅ E⁺`
  (`LocalAction.sphereEquiv`), and `ξ = sphereEquiv ∞` at `∞`; so `P = sphereEquiv ∘ ρ_1`.
  Families of pinches whose closed balls lie in one compact `K ⊆ W` are continuous, since they are
  constant `ξ` off `K` (`LocalAction.continuous_pinchFun`, as at 05:501-504).
* `P_{z,r} c` is homotopic to the identity (`LocalAction.pinch_comp_c_homotopic`): it is
  `sphereEquiv ∘ Ψ_{z,r,1} ∘ sphereEquiv⁻¹`, and `Ψ_{z,r,1} ≃ Ψ_{z,r,0} ≃ Ψ_{0,1,0} = id` by moving
  the parameters. This replaces "`P_{z,r} c` has degree one".
-/

namespace HilbertSmith.Interface

open Topology Set Metric Filter OnePoint

noncomputable section

section Blowup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The radial blow-up** `ρ_s(u) = (1 − s‖u‖)⁻¹ u` when `s‖u‖ < 1`, and `∞` otherwise. -/
def blowup (s : ℝ) (u : E) : OnePoint E :=
  if s * ‖u‖ < 1 then (((1 - s * ‖u‖)⁻¹ • u : E) : OnePoint E) else ∞

theorem blowup_of_lt {s : ℝ} {u : E} (h : s * ‖u‖ < 1) :
    blowup s u = (((1 - s * ‖u‖)⁻¹ • u : E) : OnePoint E) := by
  simp only [blowup, h, ↓reduceIte]

theorem blowup_of_le {s : ℝ} {u : E} (h : 1 ≤ s * ‖u‖) : blowup s u = ∞ := by
  simp only [blowup, not_lt.2 h, ↓reduceIte]

@[simp] theorem blowup_zero (u : E) : blowup 0 u = u := by
  simp [blowup]

omit [NormedSpace ℝ E] in
/-- A map into `E⁺` tends to `∞` when, eventually, its finite values have large norm. -/
theorem tendsto_infty_of_norm {α : Type*} {l : Filter α} {f : α → OnePoint E}
    (h : ∀ R : ℝ, ∀ᶠ a in l, ∀ u : E, f a = ↑u → R < ‖u‖) : Tendsto f l (𝓝 ∞) := by
  rw [hasBasis_nhds_infty.tendsto_right_iff]
  rintro K ⟨-, hK⟩
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  filter_upwards [h R] with a ha
  generalize f a = y at ha ⊢
  induction y using OnePoint.rec with
  | infty => exact Or.inr rfl
  | coe u =>
    refine Or.inl ⟨u, fun huK => ?_, rfl⟩
    have := mem_closedBall_zero_iff.1 (hR huK)
    linarith [ha u rfl]

/-- **The radial blow-up is continuous** in the point and the parameter. -/
theorem Continuous.blowup {X : Type*} [TopologicalSpace X] {σ : X → ℝ} {U : X → E}
    (hσ : Continuous σ) (hU : Continuous U) : Continuous fun x => blowup (σ x) (U x) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  have hm : Continuous fun x => σ x * ‖U x‖ := hσ.mul hU.norm
  by_cases h : σ x₀ * ‖U x₀‖ < 1
  · have hev : ∀ᶠ x in 𝓝 x₀, σ x * ‖U x‖ < 1 := hm.continuousAt.eventually (gt_mem_nhds h)
    have hc : ContinuousAt (fun x => (((1 - σ x * ‖U x‖)⁻¹ • U x : E) : OnePoint E)) x₀ :=
      continuous_coe.continuousAt.comp
        (((continuousAt_const.sub hm.continuousAt).inv₀ (sub_ne_zero.2 h.ne')).smul hU.continuousAt)
    refine hc.congr ?_
    filter_upwards [hev] with x hx
    rw [blowup_of_lt hx]
  · rw [not_lt] at h
    rw [ContinuousAt, blowup_of_le h]
    refine tendsto_infty_of_norm fun R => ?_
    have hU0 : 0 < ‖U x₀‖ := by
      by_contra hneg
      rw [le_antisymm (not_lt.1 hneg) (norm_nonneg _), mul_zero] at h
      linarith
    set R' := max R 0
    have hR' : 0 ≤ R' := le_max_right R 0
    have hcont : Continuous fun x => ‖U x‖ - R' * (1 - σ x * ‖U x‖) := by fun_prop
    have h0 : 0 < ‖U x₀‖ - R' * (1 - σ x₀ * ‖U x₀‖) := by nlinarith
    filter_upwards [hcont.continuousAt.eventually (lt_mem_nhds h0)] with x hx u hu
    by_cases hlt : σ x * ‖U x‖ < 1
    · rw [blowup_of_lt hlt] at hu
      obtain rfl := (coe_injective hu).symm
      have hpos : 0 < 1 - σ x * ‖U x‖ := by linarith
      rw [norm_smul, norm_inv, Real.norm_of_nonneg hpos.le, inv_mul_eq_div, lt_div_iff₀ hpos]
      nlinarith [le_max_left R 0]
    · rw [blowup_of_le (not_lt.1 hlt)] at hu
      exact absurd hu (infty_ne_coe u)

/-- **The pinch** `Ψ_{z,r,s} : E⁺ → E⁺`: `∞ ↦ ∞` and `v ↦ ρ_s((v − z)/r)`. -/
def pinchE (z : E) (r s : ℝ) (v : OnePoint E) : OnePoint E :=
  v.elim ∞ fun v => blowup s (r⁻¹ • (v - z))

@[simp] theorem pinchE_infty (z : E) (r s : ℝ) : pinchE z r s ∞ = ∞ := rfl

@[simp] theorem pinchE_coe (z : E) (r s : ℝ) (v : E) :
    pinchE z r s v = blowup s (r⁻¹ • (v - z)) := rfl

/-- `Ψ_{0,1,0}` is the identity. -/
theorem pinchE_zero_one_zero (v : OnePoint E) : pinchE 0 1 0 v = v := by
  induction v using OnePoint.rec <;> simp

/-- `Ψ_{z,r,1}` sends every point outside the closed ball `B̄(z, r)` to `∞`. -/
theorem pinchE_one_of_notMem {z v : E} {r : ℝ} (hr : 0 < r) (hv : v ∉ closedBall z r) :
    pinchE z r 1 v = ∞ := by
  rw [pinchE_coe]
  apply blowup_of_le
  rw [mem_closedBall, dist_eq_norm, not_le] at hv
  rw [one_mul, norm_smul, norm_inv, Real.norm_of_nonneg hr.le, inv_mul_eq_div, le_div_iff₀ hr]
  linarith

variable [ProperSpace E]

/-- **Pinches depend continuously on their parameters**: `(x, v) ↦ Ψ_{z(x),r(x),s(x)}(v)` is
continuous for continuous `z`, `r > 0` and `s ≥ 0`. At a finite point this is the continuity of
the blow-up; at `∞`, points of large norm are sent to points of large norm or to `∞`. -/
theorem continuous_pinchE {X : Type*} [TopologicalSpace X] {z : X → E} {r s : X → ℝ}
    (hz : Continuous z) (hr : Continuous r) (hs : Continuous s) (hr0 : ∀ x, 0 < r x)
    (hs0 : ∀ x, 0 ≤ s x) :
    Continuous fun q : X × OnePoint E => pinchE (z q.1) (r q.1) (s q.1) q.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨x₀, v₀⟩
  induction v₀ using OnePoint.rec with
  | coe v₀ =>
    have he : IsOpenEmbedding (Prod.map id ((↑) : E → OnePoint E) : X × E → X × OnePoint E) :=
      IsOpenEmbedding.id.prodMap isOpenEmbedding_coe
    refine (he.continuousAt_iff (x := (x₀, v₀))).1 ?_
    exact (Continuous.blowup (hs.comp continuous_fst)
      (((hr.comp continuous_fst).inv₀ fun q => (hr0 q.1).ne').smul
        (continuous_snd.sub (hz.comp continuous_fst)))).continuousAt
  | infty =>
    refine tendsto_infty_of_norm fun R => ?_
    set R' := max R 0
    have hR' : 0 ≤ R' := le_max_right R 0
    have h1 : ∀ᶠ x in 𝓝 x₀, ‖z x‖ < ‖z x₀‖ + 1 :=
      hz.norm.continuousAt.eventually (gt_mem_nhds (lt_add_one _))
    have h2 : ∀ᶠ x in 𝓝 x₀, r x < r x₀ + 1 :=
      hr.continuousAt.eventually (gt_mem_nhds (lt_add_one _))
    set M := R' * (r x₀ + 1) + ‖z x₀‖ + 1
    have h3 : ∀ᶠ v in 𝓝 (∞ : OnePoint E), ∀ u : E, v = ↑u → M < ‖u‖ := by
      filter_upwards [hasBasis_nhds_infty.mem_of_mem (i := closedBall (0 : E) M)
        ⟨isClosed_closedBall, isCompact_closedBall _ _⟩] with v hv u hvu
      subst hvu
      rcases hv with ⟨u', hu', huu⟩ | hv
      · obtain rfl := coe_injective huu
        simpa [mem_closedBall_zero_iff] using hu'
      · exact absurd hv (coe_ne_infty u)
    rw [nhds_prod_eq]
    filter_upwards [(h1.and h2).prod_mk h3]
    rintro ⟨x, v⟩ ⟨⟨hz1, hr1⟩, hv⟩ u hu
    induction v using OnePoint.rec with
    | infty => exact absurd hu (infty_ne_coe u)
    | coe v =>
      have hvM := hv v rfl
      have hw : R' < ‖(r x)⁻¹ • (v - z x)‖ := by
        rw [norm_smul, norm_inv, Real.norm_of_nonneg (hr0 x).le, inv_mul_eq_div,
          lt_div_iff₀ (hr0 x)]
        have := norm_sub_norm_le v (z x)
        nlinarith [mul_le_mul_of_nonneg_left hr1.le hR']
      change blowup (s x) ((r x)⁻¹ • (v - z x)) = ↑u at hu
      set w := (r x)⁻¹ • (v - z x)
      by_cases hlt : s x * ‖w‖ < 1
      · rw [blowup_of_lt hlt] at hu
        obtain rfl := (coe_injective hu).symm
        have hpos : 0 < 1 - s x * ‖w‖ := by linarith
        have hle : 1 - s x * ‖w‖ ≤ 1 := by nlinarith [hs0 x, norm_nonneg w]
        rw [norm_smul, norm_inv, Real.norm_of_nonneg hpos.le]
        calc R ≤ R' := le_max_left R 0
          _ < ‖w‖ := hw
          _ ≤ (1 - s x * ‖w‖)⁻¹ * ‖w‖ :=
            le_mul_of_one_le_left (norm_nonneg w) ((one_le_inv₀ hpos).2 hle)
      · rw [blowup_of_le (not_lt.1 hlt)] at hu
        exact absurd hu (infty_ne_coe u)

/-- The pinch `Ψ_{z,r,s}` as a continuous map, for `r > 0` and `s ≥ 0`. -/
def pinchEMap (z : E) (r s : ℝ) (hr : 0 < r) (hs : 0 ≤ s) : C(OnePoint E, OnePoint E) where
  toFun := pinchE z r s
  continuous_toFun :=
    (continuous_pinchE (X := Unit) continuous_const continuous_const continuous_const
      (fun _ => hr) fun _ => hs).comp ((continuous_const : Continuous fun _ => ()).prodMk continuous_id)

/-- **Pinches along a path of parameters are homotopic.** -/
theorem pinchEMap_homotopic {z : C(unitInterval, E)} {r s : C(unitInterval, ℝ)}
    (hr : ∀ t, 0 < r t) (hs : ∀ t, 0 ≤ s t) :
    (pinchEMap (z 0) (r 0) (s 0) (hr 0) (hs 0)).Homotopic
      (pinchEMap (z 1) (r 1) (s 1) (hr 1) (hs 1)) :=
  ⟨{ toFun := fun q => pinchE (z q.1) (r q.1) (s q.1) q.2
     continuous_toFun := continuous_pinchE z.continuous r.continuous s.continuous hr hs
     map_zero_left := fun _ => rfl
     map_one_left := fun _ => rfl }⟩

/-- **`Ψ_{z,r,1}` is homotopic to the identity**: first `Ψ_{0,1,0} = id ≃ Ψ_{z,r,0}` along
`t ↦ (t z, 1 − t + t r, 0)`, then `Ψ_{z,r,0} ≃ Ψ_{z,r,1}` along `t ↦ (z, r, t)`. -/
theorem pinchEMap_one_homotopic_id (z : E) {r : ℝ} (hr : 0 < r) :
    (pinchEMap z r 1 hr zero_le_one).Homotopic (ContinuousMap.id _) := by
  let z₁ : C(unitInterval, E) := ⟨fun t => (t : ℝ) • z, by fun_prop⟩
  let r₁ : C(unitInterval, ℝ) := ⟨fun t => 1 - t + t * r, by fun_prop⟩
  have hr₁ : ∀ t, 0 < r₁ t := fun t => by
    change 0 < 1 - (t : ℝ) + t * r
    rcases eq_or_lt_of_le t.2.2 with h1 | h1
    · rw [h1]; linarith
    · nlinarith [mul_nonneg t.2.1 hr.le]
  have h₁ := pinchEMap_homotopic (z := z₁) (r := r₁) (s := ContinuousMap.const _ 0) hr₁
    fun _ => le_rfl
  let s₂ : C(unitInterval, ℝ) := ⟨fun t => t, continuous_subtype_val⟩
  have h₂ := pinchEMap_homotopic (z := ContinuousMap.const _ z) (r := ContinuousMap.const _ r)
    (s := s₂) (fun _ => hr) fun t => t.2.1
  have e₀ : pinchEMap (z₁ 0) (r₁ 0) 0 (hr₁ 0) le_rfl = ContinuousMap.id _ :=
    ContinuousMap.ext fun v => by
      simpa [z₁, r₁, pinchEMap] using pinchE_zero_one_zero v
  have e₁ : pinchEMap (z₁ 1) (r₁ 1) 0 (hr₁ 1) le_rfl = pinchEMap z r 0 hr le_rfl :=
    ContinuousMap.ext fun v => by simp [z₁, r₁, pinchEMap]
  change (pinchEMap (z₁ 0) (r₁ 0) 0 (hr₁ 0) le_rfl).Homotopic
    (pinchEMap (z₁ 1) (r₁ 1) 0 (hr₁ 1) le_rfl) at h₁
  rw [e₀, e₁] at h₁
  change (pinchEMap z r 0 hr le_rfl).Homotopic (pinchEMap z r 1 hr zero_le_one) at h₂
  exact (h₁.trans h₂).symm

end Blowup

namespace LocalAction

variable {p : ℕ} [Fact p.Prime] {k : ℕ} (A : LocalAction p k)

/-- **Families on `W⁺` that are constant off a compact set are continuous.** If
`F : X × E → Y` is continuous and equal to `b` at every `(x, v)` with `v` outside a compact
`K ⊆ W`, then `(x, w) ↦ F(x, w)` on `X × W`, extended by `b` at `∞`, is continuous on
`X × W⁺`. -/
theorem continuous_elim_of_compact {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {K : Set A.E} (hK : IsCompact K) (hKW : K ⊆ A.W) {F : X × A.E → Y} (hF : Continuous F)
    (b : Y) (hFb : ∀ x v, v ∉ K → F (x, v) = b) :
    Continuous fun q : X × OnePoint A.W => q.2.elim b fun w => F (q.1, w) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨x₀, v₀⟩
  induction v₀ using OnePoint.rec with
  | coe w₀ =>
    have he : IsOpenEmbedding
        (Prod.map id ((↑) : A.W → OnePoint A.W) : X × A.W → X × OnePoint A.W) :=
      IsOpenEmbedding.id.prodMap isOpenEmbedding_coe
    refine (he.continuousAt_iff (x := (x₀, w₀))).1 ?_
    exact (hF.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).continuousAt
  | infty =>
    have hKw : IsCompact (((↑) : A.W → A.E) ⁻¹' K) := by
      rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.2 hKW]
      exact hK
    have hmem : (↑) '' (((↑) : A.W → A.E) ⁻¹' K)ᶜ ∪ {∞} ∈ 𝓝 (∞ : OnePoint A.W) :=
      hasBasis_nhds_infty.mem_of_mem ⟨hKw.isClosed, hKw⟩
    refine (continuousAt_const : ContinuousAt (fun _ => b) _).congr ?_
    rw [nhds_prod_eq]
    filter_upwards [prod_mem_prod univ_mem hmem]
    rintro ⟨x, v⟩ ⟨-, hv⟩
    rcases hv with ⟨w, hw, rfl⟩ | hv
    · exact (hFb x w hw).symm
    · rw [mem_singleton_iff] at hv
      subst hv
      rfl

/-- The pinch on `W⁺` as a function: `∞ ↦ ξ = sphereEquiv ∞` and `w ↦ sphereEquiv (Ψ_{z,r,1} w)`. -/
def pinchFun (z : A.E) (r : ℝ) (w : OnePoint A.W) : Sphere k :=
  w.elim (A.sphereEquiv ∞) fun w => A.sphereEquiv (pinchE z r 1 (w : A.E))

/-- **Families of pinches are continuous** when their radii are positive and their closed balls
lie in one compact subset of `W`: off that compact set they are constant `ξ` (05:501-504). -/
theorem continuous_pinchFun {X : Type*} [TopologicalSpace X] {z : X → A.E} {r : X → ℝ}
    (hz : Continuous z) (hr : Continuous r) (hr0 : ∀ x, 0 < r x) {K : Set A.E}
    (hK : IsCompact K) (hKW : K ⊆ A.W) (hball : ∀ x, closedBall (z x) (r x) ⊆ K) :
    Continuous fun q : X × OnePoint A.W => A.pinchFun (z q.1) (r q.1) q.2 := by
  refine A.continuous_elim_of_compact hK hKW
    (F := fun q : X × A.E => A.sphereEquiv (pinchE (z q.1) (r q.1) 1 q.2)) ?_ _ ?_
  · exact A.sphereEquiv.continuous.comp ((continuous_pinchE hz hr continuous_const hr0
      fun _ => zero_le_one).comp (continuous_fst.prodMk (continuous_coe.comp continuous_snd)))
  · intro x v hv
    simp only
    rw [pinchE_one_of_notMem (hr0 x) fun h => hv (hball x h)]

/-- **The pinch** `P_{z,r}` on `W⁺`, for `r > 0` and `B̄(z, r) ⊆ W` (05:156-160). -/
def pinch (z : A.E) (r : ℝ) (hr : 0 < r) (hzr : closedBall z r ⊆ A.W) :
    C(OnePoint A.W, Sphere k) where
  toFun := A.pinchFun z r
  continuous_toFun :=
    (A.continuous_pinchFun (X := Unit) continuous_const continuous_const (fun _ => hr)
      (isCompact_closedBall z r) hzr fun _ => subset_rfl).comp
      ((continuous_const : Continuous fun _ => ()).prodMk continuous_id)

theorem pinch_apply_infty (z : A.E) (r : ℝ) (hr : 0 < r) (hzr : closedBall z r ⊆ A.W) :
    A.pinch z r hr hzr ∞ = A.sphereEquiv ∞ := rfl

/-- The pinch is `ξ = sphereEquiv ∞` outside its ball. -/
theorem pinch_apply_of_notMem {z : A.E} {r : ℝ} (hr : 0 < r) (hzr : closedBall z r ⊆ A.W)
    {w : A.W} (hw : (w : A.E) ∉ closedBall z r) :
    A.pinch z r hr hzr w = A.sphereEquiv ∞ := by
  change A.sphereEquiv (pinchE z r 1 (w : A.E)) = _
  rw [pinchE_one_of_notMem hr hw]

/-- `P_{z,r} c = sphereEquiv ∘ Ψ_{z,r,1} ∘ sphereEquiv⁻¹`: off `W` both sides are `ξ`. -/
theorem pinch_comp_c (z : A.E) {r : ℝ} (hr : 0 < r) (hzr : closedBall z r ⊆ A.W) :
    (A.pinch z r hr hzr).comp A.c = ((A.sphereEquiv : C(OnePoint A.E, Sphere k)).comp
      (pinchEMap z r 1 hr zero_le_one)).comp (A.sphereEquiv.symm : C(Sphere k, OnePoint A.E)) := by
  ext1 y
  change A.pinchFun z r (collapse A.W (A.sphereEquiv.symm y)) =
    A.sphereEquiv (pinchE z r 1 (A.sphereEquiv.symm y))
  generalize A.sphereEquiv.symm y = e
  induction e using OnePoint.rec with
  | infty => rfl
  | coe v =>
    by_cases hv : v ∈ A.W
    · rw [collapse_coe_mem A.W hv]
      rfl
    · rw [collapse_coe_notMem A.W hv, pinchE_one_of_notMem hr fun h => hv (hzr h)]
      rfl

/-- **`P_{z,r} c` is homotopic to the identity** of `S^k`, OpenAI's "`P_{z,r} c` has degree one"
(05:160) without degrees. -/
theorem pinch_comp_c_homotopic (z : A.E) {r : ℝ} (hr : 0 < r) (hzr : closedBall z r ⊆ A.W) :
    ((A.pinch z r hr hzr).comp A.c).Homotopic (ContinuousMap.id _) := by
  rw [A.pinch_comp_c z hr hzr]
  have h := ((ContinuousMap.Homotopic.refl (A.sphereEquiv : C(OnePoint A.E, Sphere k))).comp
    (pinchEMap_one_homotopic_id z hr)).comp
    (ContinuousMap.Homotopic.refl (A.sphereEquiv.symm : C(Sphere k, OnePoint A.E)))
  convert h using 1
  ext1 y
  simp

end LocalAction

end

end HilbertSmith.Interface
