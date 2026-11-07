import HilbertSmith.Interface.ChartReduction
import HilbertSmith.Interface.Collapse
import HilbertSmith.Interface.GoodBases
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Lemma 5.3: the averaged test

OpenAI's Lemma 5.3 (statement 05:135-150, proof 05:152-183), in its pinch form
(`HilbertSmith.Interface.AveragedTest`): for a local action on a nonempty `W`, after replacing
`ℤ_[p]` by an open subgroup, there is `a : Y → S^d` with `a ∘ q` homotopic on `W⁺` to a pinch.

The proof is OpenAI's. Fix a pinch `P = P_{z,r}` (`LocalAction.pinch`). By compactness of `W⁺`
and continuity of the extended action (Lemma 5.2), a small open subgroup `H = p^j ℤ_[p]` moves
every value of `P` by less than `1/4`. Average over `H` with its Haar probability measure:
`A(w) = ∫_H P(h w) dμ_H(h)` is continuous, `H`-invariant and within `1/4` of `P`, so the segments
from `P` to `A` miss `0`, and normalizing them is a homotopy from `P` to the invariant map
`A/‖A‖`, which descends to `Y`. (OpenAI's bound is `1/2`; any bound below `1` works.)
-/

namespace HilbertSmith.Interface

open Topology Set Metric Filter MeasureTheory OnePoint

noncomputable section

/-- **Lemma 5.3 in pinch form** (05:135-183), proved by OpenAI's averaging argument. -/
theorem averagedTest (d : ℕ) : AveragedTest d := by
  intro p _ A hne
  obtain ⟨z, hz⟩ := hne
  obtain ⟨r₀, hr₀, hball⟩ := Metric.isOpen_iff.1 A.isOpen z hz
  set r := r₀ / 2
  have hr : 0 < r := half_pos hr₀
  have hzr : closedBall z r ⊆ A.W := (closedBall_subset_ball (half_lt_self hr₀)).trans hball
  set P := A.pinch z r hr hzr
  have := A.continuousVAdd_onePoint
  -- A small open subgroup moves every value of `P` by less than `1/4` (05:163-167).
  have hG : Continuous fun q : ℤ_[p] × OnePoint A.W =>
      ‖(P (q.1 +ᵥ q.2) : EuclideanSpace ℝ (Fin (d + 1))) - P q.2‖ :=
    ((continuous_subtype_val.comp (P.continuous.comp continuous_vadd)).sub
      (continuous_subtype_val.comp (P.continuous.comp continuous_snd))).norm
  have hev : ∀ᶠ g in 𝓝 (0 : ℤ_[p]), ∀ w ∈ (univ : Set (OnePoint A.W)),
      ‖(P (g +ᵥ w) : EuclideanSpace ℝ (Fin (d + 1))) - P w‖ < 1 / 4 :=
    isCompact_univ.eventually_forall_of_forall_eventually fun w _ =>
      hG.continuousAt.eventually (gt_mem_nhds (by simp))
  obtain ⟨t, htU, ht, h0t⟩ := _root_.mem_nhds_iff.1 hev
  obtain ⟨j, hj⟩ := exists_padicSubgroup_subset ht h0t
  set B := A.restrict j
  have := B.continuousVAdd_onePoint
  have : TopologicalSpace.MetrizableSpace (OnePoint B.W) := metrizableSpace_onePoint B.W B.isOpen
  have : LocallyCompactSpace B.W := locallyCompactSpace_coe B.W B.isOpen
  set PB := B.pinch z r hr hzr
  have hbound : ∀ (g : ℤ_[p]) (w : OnePoint B.W),
      ‖(PB (g +ᵥ w) : EuclideanSpace ℝ (Fin (d + 1))) - PB w‖ < 1 / 4 := by
    intro g w
    have hw := htU (hj (mem_padicSubgroup.2 (dvd_mul_right ((p : ℤ_[p]) ^ j) g))) w (mem_univ _)
    induction w using OnePoint.rec with
    | infty => simp
    | coe w => exact hw
  -- The Haar probability measure on `ℤ_[p]`.
  borelize ℤ_[p]
  let μ : Measure ℤ_[p] := Measure.addHaarMeasure ⊤
  have : IsProbabilityMeasure μ :=
    ⟨by simpa using
      Measure.addHaarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts ℤ_[p]))⟩
  -- The average `a'(w) = ∫ P(g + w) dμ(g)` (05:168-171).
  let F : OnePoint B.W → ℤ_[p] → EuclideanSpace ℝ (Fin (d + 1)) := fun w g => (PB (g +ᵥ w) : _)
  have hF : Continuous (Function.uncurry F) :=
    continuous_subtype_val.comp (PB.continuous.comp (continuous_vadd.comp continuous_swap))
  let a' : OnePoint B.W → EuclideanSpace ℝ (Fin (d + 1)) := fun w => ∫ g, F w g ∂μ
  have ha' : Continuous a' := by
    have := continuous_parametric_integral_of_continuous (μ := μ) hF isCompact_univ
    simpa only [Measure.restrict_univ] using this
  have hint : ∀ w, Integrable (F w) μ := fun w =>
    Integrable.of_bound (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable 1
      (ae_of_all _ fun g => (PB (g +ᵥ w)).2.le)
  have hbd : ∀ w, ‖a' w - PB w‖ ≤ 1 / 4 := by
    intro w
    have he : a' w - PB w = ∫ g, (F w g - PB w) ∂μ := by
      rw [integral_sub (hint w) (integrable_const _), integral_const, probReal_univ, one_smul]
    rw [he]
    calc ‖∫ g, (F w g - PB w) ∂μ‖ ≤ 1 / 4 * μ.real univ :=
          norm_integral_le_of_norm_le_const (ae_of_all _ fun g => (hbound g w).le)
      _ = 1 / 4 := by rw [probReal_univ, mul_one]
  have hinv : ∀ (h : ℤ_[p]) (w : OnePoint B.W), a' (h +ᵥ w) = a' w := by
    intro h w
    change ∫ g, (PB (g +ᵥ (h +ᵥ w)) : EuclideanSpace ℝ (Fin (d + 1))) ∂μ =
      ∫ g, (PB (g +ᵥ w) : EuclideanSpace ℝ (Fin (d + 1))) ∂μ
    simp_rw [← add_vadd]
    exact integral_add_right_eq_self (fun g => (PB (g +ᵥ w) : EuclideanSpace ℝ (Fin (d + 1)))) h
  -- The segments from `P` to `a'` miss `0` (05:172-174).
  have hne0 : ∀ (s : ℝ), 0 ≤ s → s ≤ 1 → ∀ w,
      (1 - s) • (PB w : EuclideanSpace ℝ (Fin (d + 1))) + s • a' w ≠ 0 := by
    intro s hs0 hs1 w h0
    have he : (1 - s) • (PB w : EuclideanSpace ℝ (Fin (d + 1))) + s • a' w =
        (PB w : EuclideanSpace ℝ (Fin (d + 1))) + s • (a' w - PB w) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    have h1 : ‖s • (a' w - PB w)‖ ≤ 1 / 4 := by
      rw [norm_smul, Real.norm_of_nonneg hs0]
      nlinarith [hbd w, norm_nonneg (a' w - PB w)]
    have h2 := norm_sub_norm_le (PB w : EuclideanSpace ℝ (Fin (d + 1))) (-(s • (a' w - PB w)))
    rw [he] at h0
    rw [sub_neg_eq_add, h0, norm_zero, norm_neg, (PB w).2] at h2
    linarith
  have ha'0 : ∀ w, a' w ≠ 0 := fun w => by simpa using hne0 1 zero_le_one le_rfl w
  -- The invariant map `a'/‖a'‖` and its descent to `Y`.
  have hnorm : ∀ w, ‖‖a' w‖⁻¹ • a' w‖ = 1 := fun w => by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 (ha'0 w))]
  let ã : C(OnePoint B.W, Sphere d) :=
    ⟨fun w => ⟨‖a' w‖⁻¹ • a' w, hnorm w⟩,
      ((ha'.norm.inv₀ fun w => norm_ne_zero_iff.2 (ha'0 w)).smul ha').subtype_mk hnorm⟩
  have hã : ∀ (h : ℤ_[p]) (w : OnePoint B.W), ã (h +ᵥ w) = ã w := fun h w =>
    Subtype.ext (by simp only [ã, ContinuousMap.coe_mk, hinv])
  let a : C(B.Y, Sphere d) :=
    ⟨Quotient.lift ã fun x y hxy => by
      obtain ⟨g, rfl⟩ := hxy
      exact hã g y, ã.continuous.quotient_lift _⟩
  refine ⟨j, a, z, r, hr, hzr, ?_⟩
  have haq : a.comp B.q = ã := ContinuousMap.ext fun _ => rfl
  rw [haq]
  refine ContinuousMap.Homotopic.symm ⟨?_⟩
  exact
    { toFun := fun q => ⟨nlerp (PB q.2 : EuclideanSpace ℝ (Fin (d + 1))) (a' q.2) q.1,
        norm_nlerp (hne0 q.1 q.1.2.1 q.1.2.2 q.2)⟩
      continuous_toFun := (Continuous.nlerp (continuous_subtype_val.comp
        (PB.continuous.comp continuous_snd)) (ha'.comp continuous_snd)
        (continuous_subtype_val.comp continuous_fst)
        fun q => hne0 q.1 q.1.2.1 q.1.2.2 q.2).subtype_mk _
      map_zero_left := fun w => Subtype.ext (nlerp_zero (PB w).2 _)
      map_one_left := fun w => Subtype.ext (by simp [nlerp, ã]) }

end

end HilbertSmith.Interface
