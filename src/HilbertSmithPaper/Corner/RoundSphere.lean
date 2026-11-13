import Mathlib

/-!
# The round sphere

`S^n = ℝ^n ∪ {∞}` is the one-point compactification `OnePoint (EuclideanSpace ℝ (Fin n))`
(`HSP.Corner.RoundSphere n`, an abbreviation, so the coercion `ℝ^n → S^n` and `∞` are Mathlib's).
The *round metric* `d_S(z, w)` is the angle between `σ⁻¹ z` and `σ⁻¹ w`, where `σ⁻¹` is the inverse
of stereographic projection from the north pole `(0, …, 0, 1)` of the unit sphere of `ℝ^{n+1}`:
`σ⁻¹ z = (2 z, |z|² - 1) / (|z|² + 1)` and `σ⁻¹ ∞ = (0, …, 0, 1)` (`HSP.Corner.invStereo`).

Lean encoding.
* `ℝ^{n+1}` is `ℝ^n × ℝ` with the Euclidean (L²) norm, `WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ)`,
  the last coordinate being the `ℝ` factor; the angle is `InnerProductGeometry.angle`.
* The metric space structure `HSP.Corner.roundMetric` is built from the angle and then its topology
  is replaced by the one-point-compactification topology, which it induces: `σ⁻¹` is a continuous
  injection of the compact space `S^n` into the unit sphere, so the identity from `S^n` to the
  angle metric is a continuous bijection from a compact space to a Hausdorff space. Hence the
  metric topology is definitionally Mathlib's `OnePoint` topology, and `S^n` is compact.
* `C_p = ZMod p` acts trivially on `S^n` (an `AddAction`, isometric), so that on a product
  `T × S^n` Mathlib's product action is the action on the first factor.
-/

open Filter Topology InnerProductGeometry

namespace HSP.Corner

/-- The sphere `S^n = ℝ^n ∪ {∞}`, the one-point compactification of Euclidean `ℝ^n`. -/
abbrev RoundSphere (n : ℕ) := OnePoint (EuclideanSpace ℝ (Fin n))

/-- Inverse stereographic projection `σ⁻¹ : S^n → ℝ^{n+1} = ℝ^n × ℝ` onto the unit sphere, from the
north pole `(0, …, 0, 1)`: `σ⁻¹ z = (2 z, |z|² - 1) / (|z|² + 1)` and `σ⁻¹ ∞ = (0, 1)`. -/
private noncomputable def invStereo {n : ℕ} (x : RoundSphere n) :
    WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ) :=
  x.elim (WithLp.toLp 2 (0, 1))
    (fun z => WithLp.toLp 2 ((2 / (‖z‖ ^ 2 + 1)) • z, (‖z‖ ^ 2 - 1) / (‖z‖ ^ 2 + 1)))

variable {n : ℕ}

private theorem invStereo_coe (z : EuclideanSpace ℝ (Fin n)) :
    invStereo (z : RoundSphere n) =
      WithLp.toLp 2 ((2 / (‖z‖ ^ 2 + 1)) • z, (‖z‖ ^ 2 - 1) / (‖z‖ ^ 2 + 1)) := rfl

private theorem invStereo_infty :
    invStereo (OnePoint.infty : RoundSphere n) = WithLp.toLp 2 (0, 1) := rfl

private theorem norm_invStereo (x : RoundSphere n) : ‖invStereo x‖ = 1 := by
  have h : ‖invStereo x‖ ^ 2 = 1 := by
    induction x using OnePoint.rec with
    | infty => rw [invStereo_infty, WithLp.prod_norm_sq_eq_of_L2]; simp
    | coe z =>
      rw [invStereo_coe, WithLp.prod_norm_sq_eq_of_L2]
      have hpos : 0 < ‖z‖ ^ 2 + 1 := by positivity
      simp only [WithLp.toLp_fst, WithLp.toLp_snd, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      field_simp
      ring
  nlinarith [norm_nonneg (invStereo x)]

private theorem invStereo_ne_zero (x : RoundSphere n) : invStereo x ≠ 0 := by
  intro h; simpa [h] using norm_invStereo x

private theorem invStereo_injective : Function.Injective (invStereo (n := n)) := by
  have key : ∀ z : EuclideanSpace ℝ (Fin n),
      1 - (‖z‖ ^ 2 - 1) / (‖z‖ ^ 2 + 1) = 2 / (‖z‖ ^ 2 + 1) := by
    intro z; have : 0 < ‖z‖ ^ 2 + 1 := by positivity
    field_simp; ring
  intro x y h
  have h2 := congrArg (fun v => (WithLp.ofLp v).2) h
  have h1 := congrArg (fun v => (WithLp.ofLp v).1) h
  induction x using OnePoint.rec with
  | infty =>
    induction y using OnePoint.rec with
    | infty => rfl
    | coe w =>
      simp only [invStereo_infty, invStereo_coe] at h2
      have := key w; rw [← h2] at this
      have : 0 < 2 / (‖w‖ ^ 2 + 1) := by positivity
      linarith
  | coe z =>
    induction y using OnePoint.rec with
    | infty =>
      simp only [invStereo_infty, invStereo_coe] at h2
      have := key z; rw [h2] at this
      have : 0 < 2 / (‖z‖ ^ 2 + 1) := by positivity
      linarith
    | coe w =>
      simp only [invStereo_coe] at h1 h2
      have hc : 2 / (‖z‖ ^ 2 + 1) = 2 / (‖w‖ ^ 2 + 1) := by rw [← key, ← key, h2]
      rw [hc] at h1
      have hne : (2 / (‖w‖ ^ 2 + 1) : ℝ) ≠ 0 := by positivity
      exact congrArg _ (smul_right_injective _ hne h1)

private theorem continuous_invStereo : Continuous (invStereo (n := n)) := by
  rw [OnePoint.continuous_iff]
  refine ⟨?_, ?_⟩
  · rw [coclosedCompact_eq_cocompact, invStereo_infty]
    have hn := tendsto_norm_cocompact_atTop (E := EuclideanSpace ℝ (Fin n))
    have hsq : Tendsto (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ 2 + 1) (cocompact _) atTop :=
      tendsto_atTop_add_const_right _ 1 ((tendsto_pow_atTop two_ne_zero).comp hn)
    have hfrac : Tendsto (fun z : EuclideanSpace ℝ (Fin n) => 2 / (‖z‖ ^ 2 + 1))
        (cocompact _) (𝓝 0) := tendsto_const_nhds.div_atTop hsq
    have h1 : Tendsto (fun z : EuclideanSpace ℝ (Fin n) => (2 / (‖z‖ ^ 2 + 1)) • z)
        (cocompact _) (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hinv : Tendsto (fun z : EuclideanSpace ℝ (Fin n) => 2 / ‖z‖) (cocompact _) (𝓝 0) :=
        tendsto_const_nhds.div_atTop hn
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hinv
        (Eventually.of_forall fun z => norm_nonneg _) ?_
      filter_upwards [hn.eventually_gt_atTop 0] with z hz
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 2 / (‖z‖ ^ 2 + 1))]
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hz]
      nlinarith [sq_nonneg ‖z‖]
    have h2 : Tendsto (fun z : EuclideanSpace ℝ (Fin n) => (‖z‖ ^ 2 - 1) / (‖z‖ ^ 2 + 1))
        (cocompact _) (𝓝 1) := by
      have : (fun z : EuclideanSpace ℝ (Fin n) => (‖z‖ ^ 2 - 1) / (‖z‖ ^ 2 + 1)) =
          fun z => 1 - 2 / (‖z‖ ^ 2 + 1) := by
        funext z; have : 0 < ‖z‖ ^ 2 + 1 := by positivity
        field_simp; ring
      rw [this]; simpa using hfrac.const_sub 1
    exact ((WithLp.prod_continuous_toLp 2 _ _).tendsto _).comp (h1.prodMk_nhds h2)
  · simp only [invStereo_coe]
    refine (WithLp.prod_continuous_toLp 2 _ _).comp (Continuous.prodMk ?_ ?_)
    · exact Continuous.smul (continuous_const.div
        (by fun_prop : Continuous fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ 2 + 1)
        fun z => by positivity) continuous_id
    · exact (by fun_prop : Continuous fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ 2 - 1).div
        (by fun_prop : Continuous fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ 2 + 1)
        fun z => by positivity

/-- `S^n` with the angle distance, before its topology is replaced. -/
private def Aux (n : ℕ) := RoundSphere n

private noncomputable instance instMetricAux (n : ℕ) : MetricSpace (Aux n) where
  dist x y := angle (invStereo (n := n) x) (invStereo y)
  dist_self x := angle_self (invStereo_ne_zero (n := n) x)
  dist_comm x y := angle_comm _ _
  dist_triangle x y z := angle_le_angle_add_angle _ _ _
  eq_of_dist_eq_zero {x y} h := by
    obtain ⟨-, r, hr, hxy⟩ := angle_eq_zero_iff.1 h
    have hr1 : r = 1 := by
      have := congrArg norm hxy
      rw [norm_smul, norm_invStereo (n := n) x, norm_invStereo (n := n) y, Real.norm_eq_abs,
        abs_of_pos hr] at this
      linarith
    exact (invStereo_injective (n := n) (by rw [hxy, hr1, one_smul])).symm

private def toAux : RoundSphere n → Aux n := id

private theorem continuousAt_angle_invStereo (x : RoundSphere n) :
    ContinuousAt (fun y : RoundSphere n => angle (invStereo y) (invStereo x)) x :=
  ContinuousAt.comp (g := fun q : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ) ×
      WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ) => angle q.1 q.2)
    (f := fun y : RoundSphere n => (invStereo y, invStereo x))
    (continuousAt_angle (x := (invStereo x, invStereo x)) (invStereo_ne_zero x)
      (invStereo_ne_zero x)) (continuous_invStereo.prodMk continuous_const).continuousAt

private theorem continuous_toAux : Continuous (toAux (n := n)) := by
  rw [continuous_iff_continuousAt]
  intro x
  have h := continuousAt_angle_invStereo x
  have h0 : angle (invStereo x) (invStereo x) = 0 := angle_self (invStereo_ne_zero x)
  rw [ContinuousAt, h0] at h
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  exact (h.eventually (gt_mem_nhds hε)).mono fun y hy => hy

private theorem topology_eq :
    (OnePoint.instTopologicalSpace : TopologicalSpace (RoundSphere n)) =
      (instMetricAux n).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace := by
  have h := ((continuous_toAux (n := n)).isClosedEmbedding (fun _ _ h => h)).isInducing.eq_induced
  exact h.trans (@induced_id (Aux n) (instMetricAux n).toUniformSpace.toTopologicalSpace)

/-- The *round metric* on `S^n`: `d_S(z, w)` is the angle between `σ⁻¹ z` and `σ⁻¹ w`. Its topology
is (definitionally) the topology of the one-point compactification, so `(S^n, d_S)` is a compact
metric space. -/
noncomputable instance roundMetric (n : ℕ) : MetricSpace (RoundSphere n) :=
  @MetricSpace.replaceTopology (RoundSphere n) _ (instMetricAux n) topology_eq

/-- The round distance is the angle between the inverse stereographic projections. -/
private theorem RoundSphere.dist_eq (x y : RoundSphere n) :
    dist x y = angle (invStereo x) (invStereo y) := rfl

/-- `C_p = ZMod p` acts trivially on the round sphere. -/
instance RoundSphere.addAction (p n : ℕ) : AddAction (ZMod p) (RoundSphere n) where
  vadd _ z := z
  zero_vadd _ := rfl
  add_vadd _ _ _ := rfl

/-- The trivial action of `C_p` on the round sphere is isometric. -/
instance RoundSphere.isIsometricVAdd (p n : ℕ) : IsIsometricVAdd (ZMod p) (RoundSphere n) :=
  ⟨fun _ => isometry_id⟩

end HSP.Corner
