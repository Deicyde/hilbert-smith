import Mathlib
import HilbertSmithPaper.ChainModels.Approximations.Modulus
import HilbertSmithPaper.ChainModels.Approximations.TrackMap
import HilbertSmithPaper.ChainModels.Approximations.TorusTestMap
import HilbertSmithPaper.ChainModels.Grid.Torus
import HilbertSmithPaper.Corner.RoundSphere
import HilbertSmithPaper.LocalData.Chart.TestMapInvariant
import HilbertSmithPaper.LocalData.Chart.TestMapContinuous
import HilbertSmithPaper.LocalData.Chart.AveragedMapDisplacement
import HilbertSmithPaper.LocalData.Control.Representatives

/-!
# Properties of completed maps

Five properties of the track family `𝓕`, its modulus `ω`, the completed maps and the torus test
map, for a local datum and a pinch radius `0 < ρ < ρ₊`.

## Encoding

* "Off `B̄(0, r)`" on the torus means `|x̃| > r` for the lift `x̃`; "off `B(0, r)`" means `|x̃| ≥ r`.
* The modulus `ω_f` of item 4 is expressed as uniform continuity of `f_T` into `(Sⁿ, d_S)`.
* `β_i` of item 5 is `trackDefect A i`, the supremum over `g, h ∈ ℤ/p^i` and `x ∈ Ω` with
  `|x| ≤ 3/8` of `|r_i(g)·(r_i(h)·x) - r_i(g+h)·x|`; the points `L(x)` are taken in `ℝⁿ`.
-/

open Filter Topology OnePoint Metric

namespace HSP.ChainModels

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- `β_i = sup {|r_i(g)·(r_i(h)·x) - r_i(g+h)·x| : g, h ∈ ℤ/p^i, |x| ≤ 3/8}`. -/
noncomputable def trackDefect (A : LocalDatum p n D ρplus) (i : ℕ) : ℝ :=
  sSup {δ | ∃ g h : ZMod (p ^ i), ∃ x : A.Ω, ‖(x : EuclideanSpace ℝ (Fin n))‖ ≤ 3 / 8 ∧
    δ = dist ((rep p i g +ᵥ (rep p i h +ᵥ x) : A.Ω) : EuclideanSpace ℝ (Fin n))
      ((rep p i (g + h) +ᵥ x : A.Ω) : EuclideanSpace ℝ (Fin n))}

/-! ### Auxiliary facts -/

/-- `d_∞(x, 0) ≤ |x̃|_2`. -/
private lemma norm_le_norm_lift (x : Torus n) : ‖x‖ ≤ ‖Torus.lift x‖ := by
  rw [← Torus.norm_ofLp_lift]
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => PiLp.norm_apply_le _ j

/-- The lift of `q(y)` is `y` when `|y|_2 < 2`. -/
private lemma lift_proj (y : EuclideanSpace ℝ (Fin n)) (hy : ‖y‖ < 2) :
    Torus.lift (Torus.proj y) = y := by
  refine PiLp.ext fun j => ?_
  have hj : |y.ofLp j| < 2 :=
    lt_of_le_of_lt (by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le y j) hy
  rw [abs_lt] at hj
  simp only [Torus.lift, Torus.proj]
  rw [AddCircle.equivIco_coe_eq (show y.ofLp j ∈ Set.Ico (-2 : ℝ) (-2 + 4) from
    ⟨by linarith, by linarith⟩)]

/-- `d_2(q y, q y') ≤ |y - y'|_2`. -/
private lemma dist₂_proj_le (y y' : EuclideanSpace ℝ (Fin n)) :
    Torus.dist₂ (Torus.proj y) (Torus.proj y') ≤ ‖y - y'‖ := by
  rw [Torus.dist₂, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ => pow_le_pow_left₀ dist_nonneg ?_ 2)
  simp only [Torus.proj, dist_eq_norm, ← AddCircle.coe_sub, WithLp.ofLp_sub, Pi.sub_apply]
  exact QuotientAddGroup.norm_mk_le_norm

private lemma continuous_proj : Continuous (Torus.proj (n := n)) :=
  continuous_pi fun j => (AddCircle.continuous_mk' (4 : ℝ)).comp
    ((continuous_apply j).comp (PiLp.continuous_ofLp 2 _))

/-- `â` moves points by at most `D`. -/
private lemma norm_completedMapEuclid_sub (A : LocalDatum p n D ρplus) (a : ℤ_[p])
    (y : EuclideanSpace ℝ (Fin n)) : ‖completedMapEuclid A a y - y‖ ≤ D := by
  unfold completedMapEuclid
  split_ifs with h
  · rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, ← dist_eq_norm]
    have h0 : 0 ≤ completedCutoff y := le_min zero_le_one (le_max_left _ _)
    have h1 : completedCutoff y ≤ 1 := min_le_left _ _
    rw [abs_of_nonneg h0]
    calc completedCutoff y * dist _ _ ≤ 1 * D :=
          mul_le_mul h1 (A.dist_vadd_le a _) dist_nonneg zero_le_one
      _ = D := one_mul D
  · simp [A.D_pos.le]

/-- Track maps move points by at most `2D`. -/
private lemma norm_trackMapEuclid_sub (A : LocalDatum p n D ρplus) (a b c : ℤ_[p])
    (t : unitInterval) (y : EuclideanSpace ℝ (Fin n)) :
    ‖trackMapEuclid A a b c t y - y‖ ≤ 2 * D := by
  have hab : ‖completedMapEuclid A a (completedMapEuclid A b y) - y‖ ≤ 2 * D := by
    have := norm_sub_le_norm_sub_add_norm_sub (completedMapEuclid A a (completedMapEuclid A b y))
      (completedMapEuclid A b y) y
    linarith [norm_completedMapEuclid_sub A a (completedMapEuclid A b y),
      norm_completedMapEuclid_sub A b y]
  have hc := norm_completedMapEuclid_sub A c y
  have heq : trackMapEuclid A a b c t y - y =
      (1 - (t : ℝ)) • (completedMapEuclid A a (completedMapEuclid A b y) - y) +
        (t : ℝ) • (completedMapEuclid A c y - y) := by
    unfold trackMapEuclid; module
  have ht0 := t.2.1
  have ht1 := t.2.2
  rw [heq]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 ht1),
    abs_of_nonneg ht0]
  nlinarith [A.D_pos]

/-- `â = a·` on `B̄(0, 1)`. -/
private lemma completedMapEuclid_of_norm_le_one (A : LocalDatum p n D ρplus) (a : ℤ_[p])
    (x : A.Ω) (hx : ‖(x : EuclideanSpace ℝ (Fin n))‖ ≤ 1) :
    completedMapEuclid A a x = ((a +ᵥ x : A.Ω) : EuclideanSpace ℝ (Fin n)) := by
  have h2 : ‖(x : EuclideanSpace ℝ (Fin n))‖ < 2 := by linarith
  have hθ : completedCutoff (x : EuclideanSpace ℝ (Fin n)) = 1 := by
    rw [completedCutoff, max_eq_right (by linarith), min_eq_left (by linarith)]
  rw [completedMapEuclid]
  simp only [h2, ↓reduceDIte, hθ, one_smul, add_sub_cancel]

/-- `â(y)` is jointly continuous in `(a, y)`. -/
private lemma continuous_completedMapEuclid (A : LocalDatum p n D ρplus) :
    Continuous fun q : ℤ_[p] × EuclideanSpace ℝ (Fin n) => completedMapEuclid A q.1 q.2 := by
  set E := EuclideanSpace ℝ (Fin n)
  refine continuous_iff_continuousAt.2 fun ⟨a₀, y₀⟩ => ?_
  by_cases hy₀ : ‖y₀‖ < 2
  · have hemb : IsOpenEmbedding
        (Prod.map id ((↑) : ball (0 : E) 2 → E) : ℤ_[p] × ball (0 : E) 2 → ℤ_[p] × E) :=
      IsOpenEmbedding.id.prodMap isOpen_ball.isOpenEmbedding_subtypeVal
    change ContinuousAt _
      (Prod.map id ((↑) : ball (0 : E) 2 → E) (a₀, ⟨y₀, mem_ball_zero_iff.2 hy₀⟩))
    rw [← hemb.continuousAt_iff]
    have hι : Continuous fun y : ball (0 : E) 2 => (⟨(y : E), A.ball_subset y.2⟩ : A.Ω) :=
      continuous_subtype_val.subtype_mk _
    have heq : (fun q : ℤ_[p] × E => completedMapEuclid A q.1 q.2) ∘
        Prod.map id ((↑) : ball (0 : E) 2 → E) =
        fun q : ℤ_[p] × ball (0 : E) 2 => (q.2 : E) + completedCutoff (q.2 : E) •
          (((q.1 +ᵥ (⟨(q.2 : E), A.ball_subset q.2.2⟩ : A.Ω) : A.Ω) : E) - q.2) := by
      funext q
      have hq := mem_ball_zero_iff.1 q.2.2
      simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq, completedMapEuclid, hq,
        ↓reduceDIte]
    rw [heq]
    have hcut : Continuous (completedCutoff (n := n)) := by unfold completedCutoff; fun_prop
    have hv : Continuous fun q : ℤ_[p] × ball (0 : E) 2 => (q.2 : E) :=
      continuous_subtype_val.comp continuous_snd
    refine Continuous.continuousAt ?_
    exact hv.add ((hcut.comp hv).smul ((continuous_subtype_val.comp
      (continuous_vadd.comp (continuous_fst.prodMk (hι.comp continuous_snd)))).sub hv))
  · have hev : (fun q : ℤ_[p] × E => completedMapEuclid A q.1 q.2) =ᶠ[𝓝 (a₀, y₀)]
        Prod.snd := by
      filter_upwards [(isOpen_lt continuous_const
        (continuous_norm.comp continuous_snd)).mem_nhds
        (show (3 / 2 : ℝ) < ‖(a₀, y₀).2‖ by simp only; linarith)] with q hq
      exact completedMapEuclid_of_le A q.1 hq.le
    exact continuousAt_snd.congr hev.symm

/-- The track maps on `ℝⁿ`, jointly continuous in all parameters. -/
private lemma continuous_trackMapEuclid (A : LocalDatum p n D ρplus) :
    Continuous fun Q : (ℤ_[p] × ℤ_[p] × ℤ_[p] × unitInterval) × EuclideanSpace ℝ (Fin n) =>
      trackMapEuclid A Q.1.1 Q.1.2.1 Q.1.2.2.1 Q.1.2.2.2 Q.2 := by
  have hc : ∀ {f : (ℤ_[p] × ℤ_[p] × ℤ_[p] × unitInterval) × EuclideanSpace ℝ (Fin n) → ℤ_[p]}
      {g : (ℤ_[p] × ℤ_[p] × ℤ_[p] × unitInterval) × EuclideanSpace ℝ (Fin n) →
        EuclideanSpace ℝ (Fin n)}, Continuous f → Continuous g →
      Continuous fun Q => completedMapEuclid A (f Q) (g Q) :=
    fun hf hg => by
      simpa only [Function.comp_def] using (continuous_completedMapEuclid A).comp (hf.prodMk hg)
  have h1 := hc (f := fun Q => Q.1.2.1) (g := Prod.snd) (by fun_prop) continuous_snd
  have h2 := hc (f := fun Q => Q.1.1) (by fun_prop) h1
  have h3 := hc (f := fun Q => Q.1.2.2.1) (g := Prod.snd) (by fun_prop) continuous_snd
  have ht : Continuous fun Q : (ℤ_[p] × ℤ_[p] × ℤ_[p] × unitInterval) ×
      EuclideanSpace ℝ (Fin n) => ((Q.1.2.2.2 : unitInterval) : ℝ) :=
    continuous_subtype_val.comp (by fun_prop)
  exact ((continuous_const.sub ht).smul h2).add (ht.smul h3)

/-- The evaluation map of the track family on the torus is continuous. -/
private lemma continuous_trackEval (A : LocalDatum p n D ρplus) :
    Continuous fun Q : (ℤ_[p] × ℤ_[p] × ℤ_[p] × unitInterval) × Torus n =>
      trackMap A Q.1.1 Q.1.2.1 Q.1.2.2.1 Q.1.2.2.2 Q.2 := by
  have hL := continuous_trackMapEuclid A
  refine continuous_iff_continuousAt.2 fun Q₀ => ?_
  by_cases hx : ‖Q₀.2‖ < 2
  · exact continuous_proj.continuousAt.comp
      (ContinuousAt.comp (f := fun Q : (ℤ_[p] × ℤ_[p] × ℤ_[p] × unitInterval) × Torus n =>
        (Q.1, Torus.lift Q.2)) hL.continuousAt
        (continuousAt_fst.prodMk (ContinuousAt.comp (g := Torus.lift (n := n)) (f := Prod.snd)
          (Torus.continuousAt_lift _ hx) continuousAt_snd)))
  · have hev : (fun Q : (ℤ_[p] × ℤ_[p] × ℤ_[p] × unitInterval) × Torus n =>
        trackMap A Q.1.1 Q.1.2.1 Q.1.2.2.1 Q.1.2.2.2 Q.2) =ᶠ[𝓝 Q₀] Prod.snd := by
      filter_upwards [(isOpen_lt continuous_const
        (continuous_norm.comp continuous_snd)).mem_nhds
        (show (3 / 2 : ℝ) < ‖Q₀.2‖ by linarith)] with Q hQ
      simp only [trackMap]
      rw [trackMapEuclid_of_le A _ _ _ _ ((lt_of_lt_of_le hQ (norm_le_norm_lift _)).le),
        Torus.proj_lift]
    exact continuousAt_snd.congr hev.symm

/-- The track family is uniformly equicontinuous. -/
private lemma equicontinuous_track (A : LocalDatum p n D ρplus) :
    ∀ ε > 0, ∃ δ > 0, ∀ L ∈ trackFamily A, ∀ x x' : Torus n,
      dist x x' < δ → dist (L x) (L x') < ε := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuous_iff.1
    (CompactSpace.uniformContinuous_of_continuous (continuous_trackEval A)) ε hε
  refine ⟨δ, hδ, ?_⟩
  rintro L ⟨q, rfl⟩ x x' hxx'
  exact h (a := (q, x)) (b := (q, x'))
    (by rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]; exact hxx')

private lemma trackOscillation_nonneg (A : LocalDatum p n D ρplus) (t : ℝ) :
    ∀ δ ∈ trackOscillation A t, 0 ≤ δ := by
  rintro δ ⟨L, -, x, x', -, rfl⟩; exact dist_nonneg

/-- The test map is `∞` at every `y` with `17/64 ≤ |y|`. -/
private lemma testMap_eq_infty (A : LocalDatum p n D ρplus) {ρ : ℝ} (hρ' : ρ < ρplus)
    (y : EuclideanSpace ℝ (Fin n)) (hy : 17 / 64 ≤ ‖y‖) :
    A.testMap ρ (y : OnePoint (EuclideanSpace ℝ (Fin n))) = ∞ := by
  by_cases hyΩ : y ∈ A.Ω
  · have h1 := A.dist_F₀_le ⟨y, hyΩ⟩
    rw [dist_eq_norm] at h1
    have h2 := norm_sub_norm_le y (A.F₀ ⟨y, hyΩ⟩)
    rw [norm_sub_rev] at h2
    have h3 : ¬ ‖A.F₀ ⟨y, hyΩ⟩‖ < ρ := fun h => by linarith [A.D_le, A.ρplus_lt]
    simp [LocalDatum.testMap, hyΩ, pinch, h3]
  · simp [LocalDatum.testMap, hyΩ]

private lemma continuous_torusTestMap (A : LocalDatum p n D ρplus) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ' : ρ < ρplus) : Continuous (torusTestMap A ρ) := by
  have hf := A.continuous_testMap hρ hρ'
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  by_cases hx₀ : ‖x₀‖ < 2
  · exact ContinuousAt.comp (g := A.testMap ρ)
      (f := fun x : Torus n => ((Torus.lift x : EuclideanSpace ℝ (Fin n)) :
        OnePoint (EuclideanSpace ℝ (Fin n))))
      hf.continuousAt (continuous_coe.continuousAt.comp (Torus.continuousAt_lift x₀ hx₀))
  · have hev : torusTestMap A ρ =ᶠ[𝓝 x₀] fun _ => ∞ := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds
        (show (17 / 64 : ℝ) < ‖x₀‖ by linarith)] with x hx
      exact testMap_eq_infty A hρ' _ (lt_of_lt_of_le hx (norm_le_norm_lift x)).le
    exact continuousAt_const.congr hev.symm

private lemma defect_bddAbove (A : LocalDatum p n D ρplus) (i : ℕ) :
    BddAbove {δ | ∃ g h : ZMod (p ^ i), ∃ x : A.Ω, ‖(x : EuclideanSpace ℝ (Fin n))‖ ≤ 3 / 8 ∧
      δ = dist ((rep p i g +ᵥ (rep p i h +ᵥ x) : A.Ω) : EuclideanSpace ℝ (Fin n))
        ((rep p i (g + h) +ᵥ x : A.Ω) : EuclideanSpace ℝ (Fin n))} := by
  refine ⟨3 * D, ?_⟩
  rintro _ ⟨g, h, x, -, rfl⟩
  have e1 := A.dist_vadd_le (rep p i g) (rep p i h +ᵥ x)
  have e2 := A.dist_vadd_le (rep p i h) x
  have e3 := A.dist_vadd_le (rep p i (g + h)) x
  rw [dist_comm] at e3
  have t1 := dist_triangle ((rep p i g +ᵥ (rep p i h +ᵥ x) : A.Ω) : EuclideanSpace ℝ (Fin n))
    ((rep p i h +ᵥ x : A.Ω) : EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n))
  have t2 := dist_triangle ((rep p i g +ᵥ (rep p i h +ᵥ x) : A.Ω) : EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) ((rep p i (g + h) +ᵥ x : A.Ω) : EuclideanSpace ℝ (Fin n))
  linarith

private lemma trackDefect_nonneg (A : LocalDatum p n D ρplus) (i : ℕ) : 0 ≤ trackDefect A i :=
  Real.sSup_nonneg (by rintro _ ⟨g, h, x, -, rfl⟩; exact dist_nonneg)

/-- *Properties of completed maps*, for a local datum and `0 < ρ < ρ₊`:
1. `ω` is nondecreasing, `ω(t) ≥ t`, `ω(t) → 0` as `t → 0`, and
   `d_∞(Lx, Lx') ≤ ω(d_∞(x, x'))` for `L ∈ 𝓕`;
2. every `L ∈ 𝓕` moves points by at most `2D` in `d_2` and is the identity off `B̄(0, 3/2)`;
3. `â = a·` on `B̄(0, 1)`, and `f_T ∘ â = f_T`;
4. `f_T` is continuous, uniformly continuous into `(Sⁿ, d_S)`, and `f_T = ∞` off `B(0, 17/64)`;
5. `β_i → 0`, and for `|x| ≤ 3/8` each `L_{r_i(g), r_i(h), r_i(g+h), t}(x)` lies within `β_i`
   of `r_i(g+h)·x`. -/
theorem completedMaps_properties (A : LocalDatum p n D ρplus) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ' : ρ < ρplus) :
    -- (1)
    (Monotone (trackModulus A) ∧ (∀ t, t ≤ trackModulus A t) ∧
      Tendsto (trackModulus A) (𝓝 0) (𝓝 0) ∧
      ∀ L ∈ trackFamily A, ∀ x x' : Torus n, dist (L x) (L x') ≤ trackModulus A (dist x x')) ∧
    -- (2)
    (∀ L ∈ trackFamily A, ∀ x : Torus n,
      Torus.dist₂ (L x) x ≤ 2 * D ∧ (3 / 2 < ‖Torus.lift x‖ → L x = x)) ∧
    -- (3)
    (∀ (a : ℤ_[p]) (x : A.Ω), ‖(x : EuclideanSpace ℝ (Fin n))‖ ≤ 1 →
      completedMapEuclid A a x = ((a +ᵥ x : A.Ω) : EuclideanSpace ℝ (Fin n))) ∧
    (∀ a : ℤ_[p], torusTestMap A ρ ∘ completedMap A a = torusTestMap A ρ) ∧
    -- (4)
    (Continuous (torusTestMap A ρ) ∧
      UniformContinuous (fun x => (torusTestMap A ρ x : Corner.RoundSphere n)) ∧
      ∀ x : Torus n, 17 / 64 ≤ ‖Torus.lift x‖ → torusTestMap A ρ x = ∞) ∧
    -- (5)
    (Tendsto (trackDefect A) atTop (𝓝 0) ∧
      ∀ (i : ℕ) (g h : ZMod (p ^ i)) (t : unitInterval) (x : A.Ω),
        ‖(x : EuclideanSpace ℝ (Fin n))‖ ≤ 3 / 8 →
        dist (trackMapEuclid A (rep p i g) (rep p i h) (rep p i (g + h)) t x)
          ((rep p i (g + h) +ᵥ x : A.Ω) : EuclideanSpace ℝ (Fin n)) ≤ trackDefect A i) := by
  set E := EuclideanSpace ℝ (Fin n)
  have hS0 : ∀ t, 0 ≤ sSup (trackOscillation A t) := fun t =>
    Real.sSup_nonneg (trackOscillation_nonneg A t)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  -- (1) monotone
  · intro t t' htt'
    have : sSup (trackOscillation A t) ≤ sSup (trackOscillation A t') := by
      rcases (trackOscillation A t).eq_empty_or_nonempty with h | h
      · rw [h, Real.sSup_empty]; exact hS0 t'
      · refine csSup_le_csSup (trackOscillation_bddAbove A t') h ?_
        rintro δ ⟨L, hL, x, x', hxx', hδ⟩
        exact ⟨L, hL, x, x', hxx'.trans htt', hδ⟩
    unfold trackModulus; linarith
  -- (1) `ω(t) ≥ t`
  · intro t; unfold trackModulus; linarith [hS0 t]
  -- (1) `ω(t) → 0`
  · have hS : Tendsto (fun t => sSup (trackOscillation A t)) (𝓝 0) (𝓝 0) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      obtain ⟨δ, hδ, h⟩ := equicontinuous_track A (ε / 2) (by positivity)
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with t ht
      rw [mem_ball, Real.dist_eq, sub_zero] at ht
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (hS0 t)]
      refine lt_of_le_of_lt (Real.sSup_le ?_ (by positivity)) (half_lt_self hε)
      rintro _ ⟨L, hL, x, x', hxx', rfl⟩
      exact (h L hL x x' (lt_of_le_of_lt hxx' (lt_of_le_of_lt (le_abs_self t) ht))).le
    have := (tendsto_id (x := 𝓝 (0 : ℝ))).add hS
    rw [add_zero] at this
    exact this
  -- (1) the modulus inequality
  · intro L hL x x'
    have := le_csSup (trackOscillation_bddAbove A (dist x x')) ⟨L, hL, x, x', le_rfl, rfl⟩
    unfold trackModulus
    linarith [dist_nonneg (x := x) (y := x')]
  -- (2)
  · rintro L ⟨q, rfl⟩ x
    constructor
    · calc Torus.dist₂ (Torus.proj (trackMapEuclid A q.1 q.2.1 q.2.2.1 q.2.2.2 (Torus.lift x))) x
          = Torus.dist₂ (Torus.proj (trackMapEuclid A q.1 q.2.1 q.2.2.1 q.2.2.2 (Torus.lift x)))
            (Torus.proj (Torus.lift x)) := by rw [Torus.proj_lift]
        _ ≤ ‖trackMapEuclid A q.1 q.2.1 q.2.2.1 q.2.2.2 (Torus.lift x) - Torus.lift x‖ :=
            dist₂_proj_le _ _
        _ ≤ 2 * D := norm_trackMapEuclid_sub A _ _ _ _ _
    · intro h
      change Torus.proj (trackMapEuclid A q.1 q.2.1 q.2.2.1 q.2.2.2 (Torus.lift x)) = x
      rw [trackMapEuclid_of_le A _ _ _ _ h.le, Torus.proj_lift]
  -- (3) `â = a·` on `B̄(0,1)`
  · exact fun a x hx => completedMapEuclid_of_norm_le_one A a x hx
  -- (3) `f_T ∘ â = f_T`
  · intro a
    funext x
    change A.testMap ρ (Torus.lift (Torus.proj (completedMapEuclid A a (Torus.lift x))) : E) =
      A.testMap ρ (Torus.lift x : E)
    by_cases h32 : 3 / 2 ≤ ‖Torus.lift x‖
    · rw [completedMapEuclid_of_le A a h32, Torus.proj_lift]
    · push Not at h32
      have hd := norm_completedMapEuclid_sub A a (Torus.lift x)
      have hu := norm_sub_norm_le (completedMapEuclid A a (Torus.lift x)) (Torus.lift x)
      have hl := norm_sub_norm_le (Torus.lift x) (completedMapEuclid A a (Torus.lift x))
      rw [norm_sub_rev] at hl
      have hlt : ‖completedMapEuclid A a (Torus.lift x)‖ < 2 := by
        linarith [A.D_le]
      rw [lift_proj _ hlt]
      by_cases h1 : ‖Torus.lift x‖ ≤ 1
      · have hyΩ : Torus.lift x ∈ A.Ω := A.ball_subset (mem_ball_zero_iff.2 (by linarith))
        have := completedMapEuclid_of_norm_le_one A a ⟨Torus.lift x, hyΩ⟩ h1
        change completedMapEuclid A a (Torus.lift x) = _ at this
        rw [this]
        exact A.testMap_vadd ρ a ⟨Torus.lift x, hyΩ⟩
      · push Not at h1
        rw [testMap_eq_infty A hρ' _ (by linarith [A.D_le]),
          testMap_eq_infty A hρ' _ (by linarith)]
  -- (4) continuity
  · exact continuous_torusTestMap A hρ hρ'
  -- (4) uniform continuity into the round sphere
  · exact CompactSpace.uniformContinuous_of_continuous (continuous_torusTestMap A hρ hρ')
  -- (4) `f_T = ∞` off `B(0, 17/64)`
  · exact fun x hx => testMap_eq_infty A hρ' _ hx
  -- (5) `β_i → 0`
  · set K : Set A.Ω := {x | ‖(x : E)‖ ≤ 3 / 8}
    have hK : IsCompact K := by
      rw [Subtype.isCompact_iff]
      have : Subtype.val '' K = closedBall (0 : E) (3 / 8) := by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩; exact mem_closedBall_zero_iff.2 hx
        · intro hy
          rw [mem_closedBall_zero_iff] at hy
          exact ⟨⟨y, A.ball_subset (mem_ball_zero_iff.2 (by linarith))⟩, hy, rfl⟩
      rw [this]; exact isCompact_closedBall _ _
    set C := (fun q : ℤ_[p] × A.Ω => q.1 +ᵥ q.2) '' (Set.univ ×ˢ K)
    have hC : IsCompact C := (isCompact_univ.prod hK).image continuous_vadd
    have hCinv : ∀ a : ℤ_[p], ∀ x ∈ C, a +ᵥ x ∈ C := by
      rintro a _ ⟨⟨b, y⟩, ⟨-, hy⟩, rfl⟩
      exact ⟨⟨a + b, y⟩, ⟨trivial, hy⟩, add_vadd a b y⟩
    have hKC : ∀ x ∈ K, x ∈ C := fun x hx => ⟨⟨0, x⟩, ⟨trivial, hx⟩, zero_vadd _ x⟩
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨L, -, hL⟩ := A.rep_vadd_close hC hCinv (half_pos hε)
    refine ⟨L, fun i hi => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (trackDefect_nonneg A i)]
    refine lt_of_le_of_lt (Real.sSup_le ?_ (by positivity)) (half_lt_self hε)
    rintro _ ⟨g, h, x, hx, rfl⟩
    exact (hL i hi g h x (hKC x hx)).le
  -- (5) the track stays within `β_i`
  · intro i g h t x hx
    have hhx : ‖((rep p i h +ᵥ x : A.Ω) : E)‖ ≤ 1 := by
      have e := A.dist_vadd_le (rep p i h) x
      rw [dist_eq_norm] at e
      linarith [norm_sub_norm_le ((rep p i h +ᵥ x : A.Ω) : E) (x : E), A.D_le]
    have hb := completedMapEuclid_of_norm_le_one A (rep p i h) x (by linarith)
    have ha := completedMapEuclid_of_norm_le_one A (rep p i g) _ hhx
    have hc := completedMapEuclid_of_norm_le_one A (rep p i (g + h)) x (by linarith)
    unfold trackMapEuclid
    rw [hb, ha, hc]
    set P := ((rep p i g +ᵥ (rep p i h +ᵥ x) : A.Ω) : E)
    set Q := ((rep p i (g + h) +ᵥ x : A.Ω) : E)
    have heq : (1 - (t : ℝ)) • P + (t : ℝ) • Q - Q = (1 - (t : ℝ)) • (P - Q) := by module
    rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 t.2.2),
      ← dist_eq_norm]
    calc (1 - (t : ℝ)) * dist P Q ≤ 1 * dist P Q :=
          mul_le_mul_of_nonneg_right (by linarith [t.2.1]) dist_nonneg
      _ = dist P Q := one_mul _
      _ ≤ trackDefect A i := le_csSup (defect_bddAbove A i) ⟨g, h, x, hx, rfl⟩

end HSP.ChainModels
