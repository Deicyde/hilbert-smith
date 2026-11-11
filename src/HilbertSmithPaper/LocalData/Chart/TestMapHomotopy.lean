import Mathlib
import HilbertSmithPaper.LocalData.Chart.TestMapContinuous
import HilbertSmithPaper.LocalData.Chart.PinchHomotopy

/-!
# The test map is homotopic to the identity

For `0 < ρ < ρplus`, the test map `f` is homotopic to the identity of `Sⁿ` relative to `{∞}`.

`H(v, x) = σ_ρ((1 - v) F₀(x) + v x)` for `x ∈ Ω` and `H(v, x) = ∞` otherwise (and at `∞`). The
argument of `σ_ρ` stays within `D` of `x`, so `H = ∞` unless `|x| < ρ + D`; hence `H` is continuous
by the gluing used for `f` (over `Ω` and over `{|x| > ρ + D}` together with `∞`). `H_0 = f`, and
`H_1 = σ_ρ` because `σ_ρ = ∞` off `B(0, ρ) ⊆ Ω`. Composing with the homotopy from the pinch to the
identity gives the claim.
-/

open Filter Topology OnePoint Metric unitInterval

namespace HSP

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

open Classical in
/-- The straight-line homotopy from the test map to the pinch, before bundling. -/
private noncomputable def lineH (A : LocalDatum p n D ρplus) (ρ v : ℝ) :
    OnePoint (EuclideanSpace ℝ (Fin n)) → OnePoint (EuclideanSpace ℝ (Fin n)) :=
  fun x => x.elim ∞ fun w =>
    if h : w ∈ A.Ω then
      pinch ρ (((1 - v) • A.F₀ ⟨w, h⟩ + v • w : EuclideanSpace ℝ (Fin n)) :
        OnePoint (EuclideanSpace ℝ (Fin n)))
    else ∞

private lemma lineH_mem (A : LocalDatum p n D ρplus) (ρ v : ℝ) (y : A.Ω) :
    lineH A ρ v ((y : EuclideanSpace ℝ (Fin n)) : OnePoint (EuclideanSpace ℝ (Fin n))) =
      pinch ρ (((1 - v) • A.F₀ y + v • (y : EuclideanSpace ℝ (Fin n)) :
        EuclideanSpace ℝ (Fin n)) : OnePoint (EuclideanSpace ℝ (Fin n))) := by
  simp [lineH]

private lemma lineH_not_mem (A : LocalDatum p n D ρplus) (ρ v : ℝ) {w : EuclideanSpace ℝ (Fin n)}
    (hw : w ∉ A.Ω) :
    lineH A ρ v (w : OnePoint (EuclideanSpace ℝ (Fin n))) = ∞ := by
  simp [lineH, hw]

/-- For `0 < ρ < ρplus`, the test map is homotopic to the identity of `Sⁿ` relative to `{∞}`. -/
theorem LocalDatum.testMap_homotopicRel_id (A : LocalDatum p n D ρplus) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ' : ρ < ρplus) :
    (⟨A.testMap ρ, A.continuous_testMap hρ hρ'⟩ : C(OnePoint (EuclideanSpace ℝ (Fin n)),
      OnePoint (EuclideanSpace ℝ (Fin n)))).HomotopicRel (ContinuousMap.id _) {∞} := by
  set E := EuclideanSpace ℝ (Fin n)
  have hρD : ρ + D < 2 := by linarith [A.ρplus_lt, A.D_le]
  -- `H = ∞` far out
  have hbig : ∀ v : I, ∀ w : E, ρ + D < ‖w‖ → lineH A ρ v (w : OnePoint E) = ∞ := by
    intro v w hw
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
      rw [show lineH A ρ v (w : OnePoint E) = lineH A ρ v (((⟨w, hwΩ⟩ : A.Ω) : E) : OnePoint E)
        from rfl, lineH_mem]
      simp [pinch, h3]
    · exact lineH_not_mem A ρ v hwΩ
  have hcont : Continuous fun q : I × OnePoint E => lineH A ρ q.1 q.2 := by
    rw [continuous_iff_continuousAt]
    rintro ⟨v₀, x₀⟩
    induction x₀ using OnePoint.rec with
    | infty =>
      have hU : ((↑) '' closedBall (0 : E) (ρ + D))ᶜ ∈ 𝓝 (∞ : OnePoint E) :=
        (OnePoint.isOpen_compl_image_coe.2
          ⟨isClosed_closedBall, isCompact_closedBall _ _⟩).mem_nhds (by simp)
      have hev : (fun q : I × OnePoint E => lineH A ρ q.1 q.2) =ᶠ[𝓝 (v₀, ∞)] fun _ => ∞ := by
        filter_upwards [prod_mem_nhds univ_mem hU] with q hq
        obtain ⟨v, x⟩ := q
        simp only [Set.mem_prod, Set.mem_univ, true_and] at hq
        induction x using OnePoint.rec with
        | infty => rfl
        | coe w =>
          refine hbig v w ?_
          by_contra hle
          exact hq ⟨w, by simpa using not_lt.1 hle, rfl⟩
      exact ContinuousAt.congr continuousAt_const hev.symm
    | coe w₀ =>
      have hemb : IsOpenEmbedding (Prod.map id ((↑) : E → OnePoint E) : I × E → I × OnePoint E) :=
        IsOpenEmbedding.id.prodMap OnePoint.isOpenEmbedding_coe
      change ContinuousAt _ (Prod.map id ((↑) : E → OnePoint E) (v₀, w₀))
      rw [← hemb.continuousAt_iff]
      by_cases hw₀ : w₀ ∈ A.Ω
      · have hembΩ : IsOpenEmbedding (Prod.map id ((↑) : A.Ω → E) : I × A.Ω → I × E) :=
          IsOpenEmbedding.id.prodMap A.isOpen_Ω.isOpenEmbedding_subtypeVal
        change ContinuousAt _ (Prod.map id ((↑) : A.Ω → E) (v₀, ⟨w₀, hw₀⟩))
        rw [← hembΩ.continuousAt_iff]
        have heq : ((fun q : I × OnePoint E => lineH A ρ q.1 q.2) ∘
            Prod.map id ((↑) : E → OnePoint E)) ∘ Prod.map id ((↑) : A.Ω → E) =
            fun q : I × A.Ω => pinch ρ (((1 - (q.1 : ℝ)) • A.F₀ q.2 + (q.1 : ℝ) • (q.2 : E) :
              E) : OnePoint E) := by
          funext q
          exact lineH_mem A ρ q.1 q.2
        rw [heq]
        refine ((continuous_pinch hρ).comp (OnePoint.continuous_coe.comp ?_)).continuousAt
        exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
          (A.continuous_F₀.comp continuous_snd)).add
          ((continuous_subtype_val.comp continuous_fst).smul
            (continuous_subtype_val.comp continuous_snd))
      · have h2 : 2 ≤ ‖w₀‖ := by
          by_contra h
          exact hw₀ (A.ball_subset (by simpa using not_le.1 h))
        have hev : ((fun q : I × OnePoint E => lineH A ρ q.1 q.2) ∘
            Prod.map id ((↑) : E → OnePoint E)) =ᶠ[𝓝 (v₀, w₀)] fun _ => ∞ := by
          filter_upwards [(isOpen_lt continuous_const
            (continuous_norm.comp continuous_snd)).mem_nhds
            (show ρ + D < ‖(v₀, w₀).2‖ by simp only; linarith)] with q hq
          exact hbig q.1 q.2 hq
        exact ContinuousAt.congr continuousAt_const hev.symm
  have F : ContinuousMap.HomotopyRel
      (⟨A.testMap ρ, A.continuous_testMap hρ hρ'⟩ : C(OnePoint E, OnePoint E))
      ⟨pinch ρ, continuous_pinch hρ⟩ {∞} :=
    { toFun := fun q => lineH A ρ q.1 q.2
      continuous_toFun := hcont
      map_zero_left := fun x => by
        induction x using OnePoint.rec with
        | infty => rfl
        | coe w =>
          by_cases hw : w ∈ A.Ω
          · change lineH A ρ 0 (((⟨w, hw⟩ : A.Ω) : E) : OnePoint E) = A.testMap ρ (w : OnePoint E)
            rw [lineH_mem]
            simp [LocalDatum.testMap, hw]
          · change lineH A ρ 0 (w : OnePoint E) = A.testMap ρ (w : OnePoint E)
            rw [lineH_not_mem A ρ 0 hw]
            simp [LocalDatum.testMap, hw]
      map_one_left := fun x => by
        induction x using OnePoint.rec with
        | infty => rfl
        | coe w =>
          by_cases hw : w ∈ A.Ω
          · change lineH A ρ 1 (((⟨w, hw⟩ : A.Ω) : E) : OnePoint E) = pinch ρ (w : OnePoint E)
            rw [lineH_mem]
            simp
          · change lineH A ρ 1 (w : OnePoint E) = pinch ρ (w : OnePoint E)
            rw [lineH_not_mem A ρ 1 hw]
            have h2 : 2 ≤ ‖w‖ := by
              by_contra h
              exact hw (A.ball_subset (by simpa using not_le.1 h))
            have : ¬ ‖w‖ < ρ := by linarith [A.D_pos]
            simp [pinch, this]
      prop' := fun t x hx => by
        rw [Set.mem_singleton_iff] at hx
        subst hx
        rfl }
  exact (ContinuousMap.HomotopicRel.trans ⟨F⟩ (pinch_homotopicRel_id hρ))

end HSP
