import Mathlib
import HilbertSmithPaper.LocalData.Control.FixedLocalData
import HilbertSmithPaper.LocalData.Chart.TestMap
import HilbertSmithPaper.LocalData.Chart.AveragedMapContinuous
import HilbertSmithPaper.LocalData.Chart.AveragedMapDisplacement
import HilbertSmithPaper.LocalData.Chart.PinchContinuous
import HilbertSmithPaper.Evaluation.CubicalPinch
import HilbertSmithPaper.ChainModels.Approximations.TorusTestMap
import HilbertSmithPaper.ChainModels.Grid.Torus

/-!
# The torus test map is homotopic to the cubical pinch

For fixed local data and every `s > 0` there is a continuous `H : [0,1] × 𝕋ⁿ → Sⁿ` with
`H(0, ·) = f_T` (the torus test map of the pinch radius `ρ`) and `H(1, ·) = κ` (the cubical pinch
for `s`). The time parameter is `unitInterval`.

## Proof

* `G(v, x) = σ_ρ((1 - v) F₀(x̃) + v x̃)` for `x̃ ∈ Ω` and `∞` otherwise. It is `∞` once
  `ρ + D < |x̃|_2`, so it is continuous on `[0,1] × ℝⁿ`; near a point of the torus with
  `|x̃|_∞ < 2` the lift is continuous, and elsewhere `G = ∞` nearby.
* `G'(v, x) = x̃ / c_v(x̃)` where `c_v(x̃) = (1 - v)(ρ - |x̃|_2) + v c_κ(x̃) > 0`, and `∞`
  otherwise. `c_v ≤ 0` once `|x̃|_∞ ≥ 1/2`, and `c_v(0) > 0`.
* The two homotopies are concatenated (`ContinuousMap.Homotopy.trans`).
-/

open OnePoint Filter Topology unitInterval

namespace HSP.Evaluation

open HSP.ChainModels

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- `|y|_∞ ≤ |y|_2`. -/
private lemma norm_ofLp_le (y : EuclideanSpace ℝ (Fin n)) : ‖WithLp.ofLp y‖ ≤ ‖y‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => PiLp.norm_apply_le y j

/-- `d_∞(x, 0) ≤ |x̃|_2`. -/
private lemma norm_le_norm_lift (x : Torus n) : ‖x‖ ≤ ‖Torus.lift x‖ := by
  rw [← Torus.norm_ofLp_lift]; exact norm_ofLp_le _

open Classical in
/-- The first stage: `σ_ρ((1 - v) F₀(w) + v w)` for `w ∈ Ω`, and `∞` otherwise. -/
private noncomputable def gFun (A : LocalDatum p n D ρplus) (ρ v : ℝ)
    (w : EuclideanSpace ℝ (Fin n)) : OnePoint (EuclideanSpace ℝ (Fin n)) :=
  if h : w ∈ A.Ω then
    pinch ρ (((1 - v) • A.F₀ ⟨w, h⟩ + v • w : EuclideanSpace ℝ (Fin n)) :
      OnePoint (EuclideanSpace ℝ (Fin n)))
  else ∞

private lemma gFun_big (A : LocalDatum p n D ρplus) (ρ : ℝ) (v : I)
    (w : EuclideanSpace ℝ (Fin n)) (hw : ρ + D < ‖w‖) : gFun A ρ v w = ∞ := by
  by_cases hwΩ : w ∈ A.Ω
  · have h1 := A.dist_F₀_le ⟨w, hwΩ⟩
    rw [dist_eq_norm] at h1
    have harg : ‖(1 - (v : ℝ)) • A.F₀ ⟨w, hwΩ⟩ + (v : ℝ) • w - w‖ ≤ D := by
      have : (1 - (v : ℝ)) • A.F₀ ⟨w, hwΩ⟩ + (v : ℝ) • w - w =
          (1 - (v : ℝ)) • (A.F₀ ⟨w, hwΩ⟩ - w) := by
        module
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 v.2.2)]
      calc (1 - (v : ℝ)) * ‖A.F₀ ⟨w, hwΩ⟩ - w‖ ≤ 1 * D := by
            apply mul_le_mul _ h1 (norm_nonneg _) zero_le_one
            linarith [v.2.1]
        _ = D := one_mul D
    have h2 := norm_sub_norm_le w ((1 - (v : ℝ)) • A.F₀ ⟨w, hwΩ⟩ + (v : ℝ) • w)
    rw [norm_sub_rev] at h2
    have h3 : ¬ ‖(1 - (v : ℝ)) • A.F₀ ⟨w, hwΩ⟩ + (v : ℝ) • w‖ < ρ := fun h => by linarith
    simp [gFun, hwΩ, pinch, h3]
  · simp [gFun, hwΩ]

/-- The first stage is continuous on `[0,1] × ℝⁿ`. -/
private lemma continuous_gFun (A : LocalDatum p n D ρplus) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ' : ρ < ρplus) :
    Continuous fun q : I × EuclideanSpace ℝ (Fin n) => gFun A ρ q.1 q.2 := by
  set E := EuclideanSpace ℝ (Fin n)
  have hρD : ρ + D < 2 := by linarith [A.ρplus_lt, A.D_le]
  rw [continuous_iff_continuousAt]
  rintro ⟨v₀, w₀⟩
  by_cases hw₀ : w₀ ∈ A.Ω
  · have hembΩ : IsOpenEmbedding (Prod.map id ((↑) : A.Ω → E) : I × A.Ω → I × E) :=
      IsOpenEmbedding.id.prodMap A.isOpen_Ω.isOpenEmbedding_subtypeVal
    change ContinuousAt _ (Prod.map id ((↑) : A.Ω → E) (v₀, ⟨w₀, hw₀⟩))
    rw [← hembΩ.continuousAt_iff]
    have heq : (fun q : I × E => gFun A ρ q.1 q.2) ∘ Prod.map id ((↑) : A.Ω → E) =
        fun q : I × A.Ω => pinch ρ (((1 - (q.1 : ℝ)) • A.F₀ q.2 + (q.1 : ℝ) • (q.2 : E) :
          E) : OnePoint E) := by
      funext q
      simp [gFun]
    rw [heq]
    refine ((continuous_pinch hρ).comp (OnePoint.continuous_coe.comp ?_)).continuousAt
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (A.continuous_F₀.comp continuous_snd)).add
      ((continuous_subtype_val.comp continuous_fst).smul
        (continuous_subtype_val.comp continuous_snd))
  · have h2 : 2 ≤ ‖w₀‖ := by
      by_contra h
      exact hw₀ (A.ball_subset (by simpa using not_le.1 h))
    have hev : (fun q : I × E => gFun A ρ q.1 q.2) =ᶠ[𝓝 (v₀, w₀)] fun _ => ∞ := by
      filter_upwards [(isOpen_lt continuous_const
        (continuous_norm.comp continuous_snd)).mem_nhds
        (show ρ + D < ‖(v₀, w₀).2‖ by simp only; linarith)] with q hq
      exact gFun_big A ρ q.1 q.2 hq
    exact ContinuousAt.congr continuousAt_const hev.symm

/-- The first stage on the torus is continuous. -/
private lemma continuous_gFun_lift (A : LocalDatum p n D ρplus) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ' : ρ < ρplus) :
    Continuous fun q : I × Torus n => gFun A ρ q.1 (Torus.lift q.2) := by
  have hg := continuous_gFun A hρ hρ'
  have hρD : ρ + D < 2 := by linarith [A.ρplus_lt, A.D_le]
  refine continuous_iff_continuousAt.2 fun ⟨v₀, x₀⟩ => ?_
  by_cases hx₀ : ‖x₀‖ < 2
  · exact ContinuousAt.comp (f := fun q : I × Torus n => (q.1, Torus.lift q.2))
      hg.continuousAt
      (continuousAt_fst.prodMk (ContinuousAt.comp (g := Torus.lift (n := n)) (f := Prod.snd)
        (Torus.continuousAt_lift x₀ hx₀) continuousAt_snd))
  · have hev : (fun q : I × Torus n => gFun A ρ q.1 (Torus.lift q.2)) =ᶠ[𝓝 (v₀, x₀)]
        fun _ => ∞ := by
      filter_upwards [(isOpen_lt continuous_const
        (continuous_norm.comp continuous_snd)).mem_nhds
        (show ρ + D < ‖(v₀, x₀).2‖ by simp only; linarith)] with q hq
      exact gFun_big A ρ q.1 _ (lt_of_lt_of_le hq (norm_le_norm_lift q.2))
    exact ContinuousAt.congr continuousAt_const hev.symm

/-- The interpolated scale `c_v(y) = (1 - v)(ρ - |y|_2) + v c_κ(y)`. -/
private noncomputable def cScale (ρ s v : ℝ) (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (1 - v) * (ρ - ‖y‖) + v * cubicalPinchScale s y

/-- The second stage: `y / c_v(y)` where `c_v(y) > 0`, and `∞` otherwise. -/
private noncomputable def hFun (ρ s v : ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    OnePoint (EuclideanSpace ℝ (Fin n)) :=
  if 0 < cScale ρ s v y then (((cScale ρ s v y)⁻¹ • y : EuclideanSpace ℝ (Fin n)) :
    OnePoint (EuclideanSpace ℝ (Fin n)))
  else ∞

private lemma continuous_cScale (ρ s : ℝ) :
    Continuous fun q : ℝ × EuclideanSpace ℝ (Fin n) => cScale ρ s q.1 q.2 := by
  have h : Continuous fun y : EuclideanSpace ℝ (Fin n) => ‖WithLp.ofLp y‖ :=
    (PiLp.continuous_ofLp 2 _).norm
  unfold cScale cubicalPinchScale
  fun_prop

private lemma cScale_nonpos {ρ s v : ℝ} (hρ : ρ < 1 / 2) (hs : 0 < s) (hv : v ∈ I)
    {y : EuclideanSpace ℝ (Fin n)} (hy : 1 / 2 ≤ ‖WithLp.ofLp y‖) : cScale ρ s v y ≤ 0 := by
  have h1 : ρ - ‖y‖ ≤ 0 := by linarith [norm_ofLp_le y]
  have h2 : cubicalPinchScale s y ≤ 0 := by
    rw [cubicalPinchScale]
    refine mul_nonpos_of_nonneg_of_nonpos (by positivity) ?_
    refine (min_le_right _ _).trans (div_nonpos_of_nonpos_of_nonneg ?_ (by norm_num))
    linarith
  have := hv.1; have := hv.2
  unfold cScale
  nlinarith

private lemma cScale_zero_pos {ρ s v : ℝ} (hρ : 0 < ρ) (hs : 0 < s) (hv : v ∈ I) :
    0 < cScale ρ s v (0 : EuclideanSpace ℝ (Fin n)) := by
  have h : cubicalPinchScale s (0 : EuclideanSpace ℝ (Fin n)) = 1 / 4 / s := by
    norm_num [cubicalPinchScale]
  have hs' : 0 < 1 / 4 / s := by positivity
  rw [cScale, h, norm_zero, sub_zero]
  rcases eq_or_lt_of_le hv.1 with h0 | h0
  · rw [← h0]; simpa using hρ
  · have := hv.2
    nlinarith

/-- The second stage on the torus is continuous. -/
private lemma continuous_hFun_lift {ρ s : ℝ} (hρ : 0 < ρ) (hρ2 : ρ < 1 / 2) (hs : 0 < s) :
    Continuous fun q : I × Torus n => hFun ρ s q.1 (Torus.lift q.2) := by
  refine continuous_iff_continuousAt.2 fun ⟨v₀, x₀⟩ => ?_
  by_cases hx₀ : ‖x₀‖ < 2
  · have hl : ContinuousAt (fun q : I × Torus n => Torus.lift q.2) (v₀, x₀) :=
      ContinuousAt.comp (g := Torus.lift (n := n)) (f := Prod.snd)
        (Torus.continuousAt_lift x₀ hx₀) continuousAt_snd
    have hc : ContinuousAt (fun q : I × Torus n => cScale ρ s q.1 (Torus.lift q.2)) (v₀, x₀) :=
      ContinuousAt.comp (f := fun q : I × Torus n => ((q.1 : ℝ), Torus.lift q.2))
        (continuous_cScale ρ s).continuousAt
        ((continuous_subtype_val.continuousAt.comp continuousAt_fst).prodMk hl)
    by_cases h0 : 0 < cScale ρ s v₀ (Torus.lift x₀)
    · have hev : ∀ᶠ q in 𝓝 (v₀, x₀), hFun ρ s q.1 (Torus.lift q.2) =
          (((cScale ρ s q.1 (Torus.lift q.2))⁻¹ • Torus.lift q.2 :
            EuclideanSpace ℝ (Fin n)) : OnePoint (EuclideanSpace ℝ (Fin n))) := by
        filter_upwards [hc.eventually (lt_mem_nhds h0)] with q hq
        simp [hFun, hq]
      refine ContinuousAt.congr ?_ (EventuallyEq.symm hev)
      exact continuous_coe.continuousAt.comp ((hc.inv₀ h0.ne').smul hl)
    · have hh0 : hFun ρ s v₀ (Torus.lift x₀) = ∞ := by simp [hFun, h0]
      have hne : Torus.lift x₀ ≠ 0 := by
        intro h
        rw [h] at h0
        exact h0 (cScale_zero_pos hρ hs v₀.2)
      set a := ‖Torus.lift x₀‖ with ha_def
      have ha : 0 < a := norm_pos_iff.2 hne
      rw [ContinuousAt]
      change Tendsto _ _ (𝓝 (hFun ρ s v₀ (Torus.lift x₀)))
      rw [hh0]
      refine le_nhds_infty.2 fun K _ hK => ?_
      obtain ⟨M, hM⟩ := hK.isBounded.subset_closedBall 0
      set M' := max M 1
      have hM' : 0 < M' := lt_of_lt_of_le one_pos (le_max_right _ _)
      have e1 : ∀ᶠ q in 𝓝 (v₀, x₀), a / 2 < ‖Torus.lift q.2‖ :=
        (continuous_norm.continuousAt.comp hl).eventually (lt_mem_nhds (show a / 2 < ‖Torus.lift x₀‖ by linarith))
      have e2 : ∀ᶠ q in 𝓝 (v₀, x₀), cScale ρ s q.1 (Torus.lift q.2) < a / (2 * M') :=
        hc.eventually (gt_mem_nhds (lt_of_le_of_lt (not_lt.1 h0) (by positivity)))
      rw [Filter.mem_map]
      filter_upwards [e1, e2] with q hq1 hq2
      by_cases hpos : 0 < cScale ρ s q.1 (Torus.lift q.2)
      · left
        refine ⟨(cScale ρ s q.1 (Torus.lift q.2))⁻¹ • Torus.lift q.2, ?_,
          by simp [hFun, hpos]⟩
        intro hv
        have hvM : ‖(cScale ρ s q.1 (Torus.lift q.2))⁻¹ • Torus.lift q.2‖ ≤ M' := by
          have := hM hv; rw [Metric.mem_closedBall, dist_zero_right] at this
          exact this.trans (le_max_left _ _)
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos,
          inv_mul_le_iff₀ hpos] at hvM
        have h3 := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * M')).1 hq2
        nlinarith
      · right
        simp [hFun, hpos]
  · have hev : (fun q : I × Torus n => hFun ρ s q.1 (Torus.lift q.2)) =ᶠ[𝓝 (v₀, x₀)]
        fun _ => ∞ := by
      filter_upwards [(isOpen_lt continuous_const
        (continuous_norm.comp continuous_snd)).mem_nhds
        (show (1 / 2 : ℝ) < ‖(v₀, x₀).2‖ by simp only; linarith)] with q hq
      have : ¬ 0 < cScale ρ s q.1 (Torus.lift q.2) := not_lt.2 <|
        cScale_nonpos hρ2 hs q.1.2 (by rw [Torus.norm_ofLp_lift]; exact hq.le)
      simp [hFun, this]
    exact ContinuousAt.congr continuousAt_const hev.symm

/-- *The torus test map is homotopic to the cubical pinch*: for fixed local data and `s > 0`
there is a continuous `H : [0,1] × 𝕋ⁿ → Sⁿ` with `H(0,x) = f_T(x)` and `H(1,x) = κ(x)`. -/
theorem torusTestMap_homotopic_pinch (F : FixedLocalData p n D ρplus) {s : ℝ} (hs : 0 < s) :
    ∃ H : unitInterval × Torus n → OnePoint (EuclideanSpace ℝ (Fin n)), Continuous H ∧
      (∀ x, H (0, x) = torusTestMap F.toLocalDatum F.ρ x) ∧
      ∀ x, H (1, x) = cubicalPinch n s hs x := by
  set A := F.toLocalDatum
  set E := EuclideanSpace ℝ (Fin n)
  have hρ := F.ρ_pos
  have hρ2 : F.ρ < 1 / 2 := by linarith [F.ρ_lt, A.ρplus_lt]
  have hG := continuous_gFun_lift A hρ F.ρ_lt
  have hG' := continuous_hFun_lift (n := n) hρ hρ2 hs
  set G : I × Torus n → OnePoint E := fun q => gFun A F.ρ q.1 (Torus.lift q.2) with hGdef
  set G' : I × Torus n → OnePoint E := fun q => hFun F.ρ s q.1 (Torus.lift q.2) with hG'def
  have hsec : ∀ t : I, Continuous fun x : Torus n => (t, x) :=
    fun t => continuous_const.prodMk continuous_id
  let F1 : ContinuousMap.Homotopy (⟨fun x => G (0, x), hG.comp (hsec 0)⟩ : C(Torus n, OnePoint E))
      ⟨fun x => G (1, x), hG.comp (hsec 1)⟩ :=
    { toFun := G, continuous_toFun := hG, map_zero_left := fun _ => rfl,
      map_one_left := fun _ => rfl }
  let F2 : ContinuousMap.Homotopy (⟨fun x => G' (0, x), hG'.comp (hsec 0)⟩ :
      C(Torus n, OnePoint E)) ⟨fun x => G' (1, x), hG'.comp (hsec 1)⟩ :=
    { toFun := G', continuous_toFun := hG', map_zero_left := fun _ => rfl,
      map_one_left := fun _ => rfl }
  have hmid : (⟨fun x => G' (0, x), hG'.comp (hsec 0)⟩ : C(Torus n, OnePoint E)) =
      ⟨fun x => G (1, x), hG.comp (hsec 1)⟩ := by
    ext x
    change hFun F.ρ s ((0 : I) : ℝ) (Torus.lift x) = gFun A F.ρ ((1 : I) : ℝ) (Torus.lift x)
    simp only [Set.Icc.coe_zero, Set.Icc.coe_one]
    by_cases hw : Torus.lift x ∈ A.Ω
    · simp [hFun, gFun, hw, cScale, pinch, sub_pos]
    · have h2 : 2 ≤ ‖Torus.lift x‖ := by
        by_contra h
        exact hw (A.ball_subset (by simpa using not_le.1 h))
      have : ¬ 0 < (1 - 0) * (F.ρ - ‖Torus.lift x‖) + 0 * cubicalPinchScale s (Torus.lift x) := by
        intro h; linarith
      simp only [hFun, gFun, hw, cScale, this, ite_false, dite_false]
  refine ⟨F1.trans (F2.cast hmid rfl), (F1.trans (F2.cast hmid rfl)).continuous,
    fun x => ?_, fun x => ?_⟩
  · rw [ContinuousMap.Homotopy.apply_zero]
    change gFun A F.ρ ((0 : I) : ℝ) (Torus.lift x) = A.testMap F.ρ (Torus.lift x)
    by_cases hw : Torus.lift x ∈ A.Ω
    · simp [gFun, LocalDatum.testMap, hw]
    · simp [gFun, LocalDatum.testMap, hw]
  · rw [ContinuousMap.Homotopy.apply_one]
    change hFun F.ρ s ((1 : I) : ℝ) (Torus.lift x) = _
    rw [cubicalPinch_apply]
    simp [hFun, cScale]

end HSP.Evaluation
