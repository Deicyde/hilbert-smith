import HilbertSmith.Interface.Spaces

/-!
# The close-pair test and homotopies of sphere-valued maps

The topology behind Proposition 6.6 of OpenAI's preprint (homotopy of character classes),
without any sheaves.

* `Sphere d` and `ClosePair d` are compact Hausdorff.
* `ClosePair.π₀`, `ClosePair.π₁`: the two projections `C_d → S^d`, and `ClosePair.homotopic_π`:
  they are homotopic, by normalized linear interpolation (06:369-375).
* `ClosePair.eq_of_homotopic`: an invariant of maps `Y → S^d` (with `Y` compact) that takes the
  same value on `π₀ ∘ s` and `π₁ ∘ s` for every `s : Y → C_d` takes the same value on homotopic
  maps. This is the subdivision argument of the proof of Proposition 6.6 (06:377-391): uniform
  continuity of the homotopy gives stages `r₀ < ⋯ < r_N` with consecutive stages close, and each
  close pair is a map into `C_d`.
-/

namespace HilbertSmith.Interface

open Topology Set

variable {d : ℕ}

/-- The sphere is compact. -/
instance : CompactSpace (Sphere d) := by
  have h : IsCompact {x : EuclideanSpace ℝ (Fin (d + 1)) | ‖x‖ = 1} := by
    simpa [Metric.sphere] using isCompact_sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1
  exact isCompact_iff_compactSpace.mp h

/-- The close-pair test is compact: a closed subset of `S^d × S^d`. -/
instance : CompactSpace (ClosePair d) := by
  have h : IsClosed {z : Sphere d × Sphere d |
      0 ≤ inner ℝ (z.1 : EuclideanSpace ℝ (Fin (d + 1))) z.2} :=
    isClosed_le continuous_const (by fun_prop)
  exact isCompact_iff_compactSpace.mp h.isCompact

/-- Two points of `S^d` at distance less than `1` have nonnegative inner product, since
`‖x - y‖² = 2 - 2⟨x, y⟩` for unit vectors (any bound `≤ √2` would do). -/
theorem Sphere.inner_nonneg_of_dist_lt_one {x y : Sphere d} (h : dist x y < 1) :
    0 ≤ inner ℝ (x : EuclideanSpace ℝ (Fin (d + 1))) y := by
  have hxy : ‖(x : EuclideanSpace ℝ (Fin (d + 1))) - y‖ < 1 := by
    rwa [Subtype.dist_eq, dist_eq_norm] at h
  have key := norm_sub_sq_real (x : EuclideanSpace ℝ (Fin (d + 1))) y
  rw [x.2, y.2] at key
  nlinarith [norm_nonneg ((x : EuclideanSpace ℝ (Fin (d + 1))) - y)]

namespace ClosePair

variable (d)

/-- The first projection `π₀ : C_d → S^d`. -/
def π₀ : C(ClosePair d, Sphere d) := ⟨fun z => z.1.1, by fun_prop⟩

/-- The second projection `π₁ : C_d → S^d`. -/
def π₁ : C(ClosePair d, Sphere d) := ⟨fun z => z.1.2, by fun_prop⟩

/-- The linear interpolation `(1 − r)x₀ + r x₁` between the two points of a close pair. -/
noncomputable def interp (p : unitInterval × ClosePair d) : EuclideanSpace ℝ (Fin (d + 1)) :=
  (1 - (p.1 : ℝ)) • (p.2.1.1 : EuclideanSpace ℝ (Fin (d + 1))) + (p.1 : ℝ) • (p.2.1.2 : _)

/-- The interpolation is continuous. -/
theorem continuous_interp : Continuous (interp d) := by
  unfold interp
  fun_prop

/-- The interpolation never vanishes: its squared norm is
`(1 − r)² + r² + 2r(1 − r)⟨x₀, x₁⟩ ≥ (1 − r)² + r² > 0`. -/
theorem norm_interp_ne_zero (p : unitInterval × ClosePair d) : ‖interp d p‖ ≠ 0 := by
  obtain ⟨⟨r, hr0, hr1⟩, ⟨⟨x₀, x₁⟩, hx⟩⟩ := p
  have key : ‖interp d (⟨r, hr0, hr1⟩, ⟨⟨x₀, x₁⟩, hx⟩)‖ ^ 2 =
      (1 - r) ^ 2 + r ^ 2 +
        2 * (r * (1 - r)) * inner ℝ (x₀ : EuclideanSpace ℝ (Fin (d + 1))) x₁ := by
    simp only [interp, norm_add_sq_real, norm_smul, real_inner_smul_left, real_inner_smul_right,
      x₀.2, x₁.2, Real.norm_eq_abs, abs_of_nonneg hr0, abs_of_nonneg (sub_nonneg.mpr hr1)]
    ring
  intro h
  rw [h] at key
  nlinarith [mul_nonneg (mul_nonneg hr0 (sub_nonneg.mpr hr1)) hx]

/-- The projections `π₀, π₁ : C_d → S^d` are homotopic, by
`(x₀, x₁, r) ↦ ((1 − r)x₀ + r x₁) / ‖(1 − r)x₀ + r x₁‖`; the denominator is nonzero because its
square is `(1 − r)² + r² + 2r(1 − r)⟨x₀, x₁⟩ ≥ 1/2` (06:369-375). -/
theorem homotopic_π : (π₀ d).Homotopic (π₁ d) := by
  refine ⟨{
    toFun := fun p => ⟨‖interp d p‖⁻¹ • interp d p, by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_interp_ne_zero d p)]⟩
    continuous_toFun := by
      have hinv : Continuous fun p => ‖interp d p‖⁻¹ :=
        (continuous_norm.comp (continuous_interp d)).inv₀ (norm_interp_ne_zero d)
      exact (hinv.smul (continuous_interp d)).subtype_mk _
    map_zero_left := fun z => by
      apply Subtype.ext
      simp [interp, π₀, z.1.1.2]
    map_one_left := fun z => by
      apply Subtype.ext
      simp [interp, π₁, z.1.2.2] }⟩

variable {d}

/-- **The subdivision argument of Proposition 6.6** (06:377-391). Let `Y` be compact and let `Z`
be any function of maps `Y → S^d` with `Z (π₀ ∘ s) = Z (π₁ ∘ s)` for every `s : Y → C_d`. Then
homotopic maps have the same value of `Z`. -/
theorem eq_of_homotopic {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] {α : Sort*}
    (Z : C(Y, Sphere d) → α)
    (hZ : ∀ s : C(Y, ClosePair d), Z ((π₀ d).comp s) = Z ((π₁ d).comp s))
    {t₀ t₁ : C(Y, Sphere d)} (h : t₀.Homotopic t₁) : Z t₀ = Z t₁ := by
  obtain ⟨H⟩ := h
  -- Uniform continuity of `r ↦ H(r, ·)` into the sup metric on `C(Y, S^d)`.
  obtain ⟨δ, hδ, hH⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous H.curry.continuous) 1 one_pos
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  -- The stages `r_j = j / (N + 1)`, truncated to `[0, 1]`.
  let r : ℕ → unitInterval := fun j => Set.projIcc 0 1 zero_le_one (j / (N + 1 : ℝ))
  have hr : ∀ j, dist (r j) (r (j + 1)) < δ := by
    intro j
    rw [Subtype.dist_eq, Real.dist_eq]
    refine (Set.abs_projIcc_sub_projIcc _).trans_lt ?_
    rw [← neg_sub, abs_neg, Nat.cast_succ, add_div, add_sub_cancel_left, abs_of_pos (by positivity)]
    exact hN
  have hstep : ∀ j, Z (H.curry (r j)) = Z (H.curry (r (j + 1))) := by
    intro j
    let s : C(Y, ClosePair d) :=
      ⟨fun y => ⟨(H (r j, y), H (r (j + 1), y)), Sphere.inner_nonneg_of_dist_lt_one <|
        (ContinuousMap.dist_apply_le_dist y).trans_lt (hH (hr j))⟩, by fun_prop⟩
    have h₀ : (π₀ d).comp s = H.curry (r j) := rfl
    have h₁ : (π₁ d).comp s = H.curry (r (j + 1)) := rfl
    rw [← h₀, ← h₁, hZ]
  have hchain : ∀ n, Z (H.curry (r 0)) = Z (H.curry (r n)) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => exact ih.trans (hstep n)
  have hr0 : r 0 = 0 := by simp [r]
  have hrN : r (N + 1) = 1 := by
    simp only [r]
    rw [Nat.cast_succ, div_self (by positivity)]
    simp
  have e₀ : H.curry 0 = t₀ := by ext y; simp
  have e₁ : H.curry 1 = t₁ := by ext y; simp
  have := hchain (N + 1)
  rwa [hr0, hrN, e₀, e₁] at this

end ClosePair

end HilbertSmith.Interface
