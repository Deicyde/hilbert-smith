import Mathlib
import HilbertSmithPaper.LocalData.Chart.PinchContinuous

/-!
# The pinch is homotopic to the identity

For `ρ > 0`, `σ_ρ` is homotopic to the identity of `Sⁿ = OnePoint ℝⁿ` relative to `{∞}`.

With `c_t = (1 - t) + t ρ > 0`, put `G(t, x) = x / (c_t - t|x|)` where `x ∈ ℝⁿ` and `t|x| < c_t`,
and `G(t, x) = ∞` elsewhere. Then `G_0 = id`, `G_1 = σ_ρ` and `G(t, ∞) = ∞`. `G` is continuous: on
the open set `t|x| < c_t` by the formula; where `t|x| > c_t` it is constant; at the blow-up locus
`c_t - t|x| → 0` while `|x|` stays near a positive value; near `∞`, `|G(t, x)| ≥ |x| / c_t ≥
|x| / max(1, ρ)` wherever `G` is finite.
-/

open Filter Topology OnePoint Metric unitInterval

namespace HSP

variable {n : ℕ}

/-- The generalized pinch `x ↦ x / (a - b|x|)` on `{b|x| < a}`, and `∞` elsewhere. -/
private noncomputable def gen (a b : ℝ) :
    OnePoint (EuclideanSpace ℝ (Fin n)) → OnePoint (EuclideanSpace ℝ (Fin n)) :=
  fun x => x.elim ∞ fun v =>
    if b * ‖v‖ < a then ((a - b * ‖v‖)⁻¹ • v : EuclideanSpace ℝ (Fin n)) else ∞

private lemma gen_coe (a b : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    gen a b (v : OnePoint (EuclideanSpace ℝ (Fin n))) =
      if b * ‖v‖ < a then
        (((a - b * ‖v‖)⁻¹ • v : EuclideanSpace ℝ (Fin n)) : OnePoint (EuclideanSpace ℝ (Fin n)))
      else ∞ := rfl

private lemma continuous_gen {a b : I → ℝ} (ha : Continuous a) (hb : Continuous b)
    (hapos : ∀ t, 0 < a t) (hbnn : ∀ t, 0 ≤ b t) {K : ℝ} (hK : ∀ t, a t ≤ K) :
    Continuous fun q : I × OnePoint (EuclideanSpace ℝ (Fin n)) => gen (a q.1) (b q.1) q.2 := by
  set E := EuclideanSpace ℝ (Fin n)
  have hKpos : 0 < K := (hapos 0).trans_le (hK 0)
  -- the norm of a finite value is large when `|v|` is large
  have hbig : ∀ t (v : E), b t * ‖v‖ < a t → ‖v‖ / K ≤ ‖((a t - b t * ‖v‖)⁻¹ • v : E)‖ := by
    intro t v hv
    have hpos : 0 < a t - b t * ‖v‖ := sub_pos.2 hv
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos), inv_mul_eq_div]
    apply div_le_div_of_nonneg_left (norm_nonneg v) hpos
    linarith [hK t, mul_nonneg (hbnn t) (norm_nonneg v)]
  rw [continuous_iff_continuousAt]
  rintro ⟨t₀, x₀⟩
  induction x₀ using OnePoint.rec with
  | infty =>
    change Tendsto _ _ (𝓝 (gen (a t₀) (b t₀) (∞ : OnePoint E)))
    change Tendsto _ _ (𝓝 (∞ : OnePoint E))
    rw [Tendsto, le_nhds_infty]
    intro s _ hsc
    obtain ⟨R, hR⟩ := hsc.isBounded.subset_closedBall (0 : E)
    set R' := max R 0
    have hU : ((↑) '' closedBall (0 : E) (R' * K + 1))ᶜ ∈ 𝓝 (∞ : OnePoint E) :=
      (OnePoint.isOpen_compl_image_coe.2 ⟨isClosed_closedBall, isCompact_closedBall _ _⟩).mem_nhds
        (by simp)
    rw [mem_map]
    filter_upwards [prod_mem_nhds univ_mem hU] with q hq
    obtain ⟨t, x⟩ := q
    simp only [Set.mem_prod, Set.mem_univ, true_and] at hq
    induction x using OnePoint.rec with
    | infty => right; rfl
    | coe v =>
      simp only [Set.mem_preimage]
      rw [gen_coe]
      have hv : R' * K + 1 < ‖v‖ := by
        by_contra hle
        exact hq ⟨v, by simpa using not_lt.1 hle, rfl⟩
      split_ifs with hlt
      · left
        refine ⟨_, fun hs => ?_, rfl⟩
        have h1 := hR hs
        rw [mem_closedBall, dist_zero_right] at h1
        have h2 := hbig t v hlt
        have h3 : R' < ‖v‖ / K := by
          rw [lt_div_iff₀ hKpos]
          linarith
        linarith [le_max_left R 0]
      · right; rfl
  | coe v₀ =>
    have hemb : IsOpenEmbedding (Prod.map id ((↑) : E → OnePoint E) : I × E → I × OnePoint E) :=
      IsOpenEmbedding.id.prodMap OnePoint.isOpenEmbedding_coe
    change ContinuousAt _ (Prod.map id ((↑) : E → OnePoint E) (t₀, v₀))
    rw [← hemb.continuousAt_iff]
    set g : I × E → OnePoint E := fun q => gen (a q.1) (b q.1) (q.2 : OnePoint E)
    change ContinuousAt g (t₀, v₀)
    have hd : Continuous fun q : I × E => a q.1 - b q.1 * ‖q.2‖ :=
      (ha.comp continuous_fst).sub
        ((hb.comp continuous_fst).mul (continuous_norm.comp continuous_snd))
    rcases lt_trichotomy (b t₀ * ‖v₀‖) (a t₀) with h | h | h
    · have hev : g =ᶠ[𝓝 (t₀, v₀)] fun q =>
          (((a q.1 - b q.1 * ‖q.2‖)⁻¹ • q.2 : E) : OnePoint E) := by
        filter_upwards [(isOpen_lt ((hb.comp continuous_fst).mul
          (continuous_norm.comp continuous_snd)) (ha.comp continuous_fst)).mem_nhds h] with q hq
        have hq' : b q.1 * ‖q.2‖ < a q.1 := hq
        change gen (a q.1) (b q.1) (q.2 : OnePoint E) = _
        rw [gen_coe]
        simp only [hq', ↓reduceIte]
      refine ContinuousAt.congr ?_ hev.symm
      refine OnePoint.continuous_coe.continuousAt.comp ?_
      exact (hd.continuousAt.inv₀ (sub_pos.2 h).ne').smul continuous_snd.continuousAt
    · -- the blow-up locus
      have hv₀ : 0 < ‖v₀‖ := by
        rcases (norm_nonneg v₀).lt_or_eq with hv | hv
        · exact hv
        · rw [← hv, mul_zero] at h
          exact absurd h (hapos t₀).ne
      change Tendsto g _ (𝓝 (gen (a t₀) (b t₀) (v₀ : OnePoint E)))
      have hinf : gen (a t₀) (b t₀) (v₀ : OnePoint E) = ∞ := by
        rw [gen_coe, h]
        simp
      rw [hinf, Tendsto, le_nhds_infty]
      intro s _ hsc
      obtain ⟨R, hR⟩ := hsc.isBounded.subset_closedBall (0 : E)
      set R' := max R 0
      set δ := ‖v₀‖ / (2 * (R' + 1))
      have hR'1 : 0 < R' + 1 := by positivity
      have hδ : 0 < δ := by positivity
      have hn1 : ∀ᶠ q in 𝓝 (t₀, v₀), ‖v₀‖ / 2 < ‖q.2‖ :=
        ((continuous_norm.comp continuous_snd).tendsto (t₀, v₀)).eventually
          (lt_mem_nhds (half_lt_self hv₀))
      have hn2 : ∀ᶠ q in 𝓝 (t₀, v₀), a q.1 - b q.1 * ‖q.2‖ < δ :=
        (hd.tendsto (t₀, v₀)).eventually (gt_mem_nhds (by simp only; rw [h, sub_self]; exact hδ))
      rw [mem_map]
      filter_upwards [hn1, hn2] with q hq1 hq2
      change gen (a q.1) (b q.1) (q.2 : OnePoint E) ∈ ((↑) '' sᶜ ∪ {∞} : Set (OnePoint E))
      rw [gen_coe]
      split_ifs with hlt
      · left
        refine ⟨_, fun hs => ?_, rfl⟩
        have h1 := hR hs
        rw [mem_closedBall, dist_zero_right] at h1
        have hpos : 0 < a q.1 - b q.1 * ‖q.2‖ := sub_pos.2 hlt
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos), inv_mul_eq_div,
          div_le_iff₀ hpos] at h1
        have hq1' : ‖v₀‖ / 2 < ‖q.2‖ := hq1
        have hq2' : a q.1 - b q.1 * ‖q.2‖ < δ := hq2
        have h2 : R * (a q.1 - b q.1 * ‖q.2‖) ≤ R' * (a q.1 - b q.1 * ‖q.2‖) :=
          mul_le_mul_of_nonneg_right (le_max_left R 0) hpos.le
        have h2' : R' * (a q.1 - b q.1 * ‖q.2‖) ≤ R' * δ :=
          mul_le_mul_of_nonneg_left hq2'.le (le_max_right R 0)
        have h3 : R' * δ < ‖v₀‖ / 2 := by
          have : R' * δ = ‖v₀‖ / 2 * (R' / (R' + 1)) := by
            simp only [δ]; field_simp
          rw [this]
          have : R' / (R' + 1) < 1 := (div_lt_one hR'1).2 (lt_add_one R')
          nlinarith
        linarith
      · right; rfl
    · have hev : g =ᶠ[𝓝 (t₀, v₀)] fun _ => ∞ := by
        filter_upwards [(isOpen_lt (ha.comp continuous_fst) ((hb.comp continuous_fst).mul
          (continuous_norm.comp continuous_snd))).mem_nhds h] with q hq
        have hq' : ¬ b q.1 * ‖q.2‖ < a q.1 := not_lt.2 (le_of_lt hq)
        change gen (a q.1) (b q.1) (q.2 : OnePoint E) = _
        rw [gen_coe]
        simp only [hq', ↓reduceIte]
      exact ContinuousAt.congr continuousAt_const hev.symm

/-- For `ρ > 0`, the pinch `σ_ρ` is homotopic to the identity of `Sⁿ` relative to `{∞}`. -/
theorem pinch_homotopicRel_id {ρ : ℝ} (hρ : 0 < ρ) :
    (⟨pinch ρ, continuous_pinch hρ⟩ : C(OnePoint (EuclideanSpace ℝ (Fin n)),
      OnePoint (EuclideanSpace ℝ (Fin n)))).HomotopicRel (ContinuousMap.id _) {∞} := by
  set E := EuclideanSpace ℝ (Fin n)
  set c : I → ℝ := fun t => 1 - (t : ℝ) + (t : ℝ) * ρ
  have hc : Continuous c := by fun_prop
  have hcpos : ∀ t, 0 < c t := by
    intro t
    have h0 := t.2.1
    have h1 := t.2.2
    simp only [c]
    rcases eq_or_lt_of_le h1 with h | h
    · rw [h]; linarith
    · linarith [mul_nonneg h0 hρ.le]
  have hcK : ∀ t, c t ≤ 1 + ρ := by
    intro t
    have h0 := t.2.1
    have h1 := t.2.2
    simp only [c]
    linarith [mul_le_mul_of_nonneg_right h1 hρ.le]
  have hG := continuous_gen (n := n) hc continuous_subtype_val hcpos (fun t => t.2.1) hcK
  refine ContinuousMap.HomotopicRel.symm ⟨?_⟩
  exact
    { toFun := fun q => gen (c q.1) (q.1 : ℝ) q.2
      continuous_toFun := hG
      map_zero_left := fun x => by
        induction x using OnePoint.rec with
        | infty => rfl
        | coe v =>
          simp [gen_coe, c]
      map_one_left := fun x => by
        induction x using OnePoint.rec with
        | infty => rfl
        | coe v =>
          simp [gen_coe, c, pinch]
      prop' := fun t x hx => by
        rw [Set.mem_singleton_iff] at hx
        subst hx
        rfl }

end HSP
