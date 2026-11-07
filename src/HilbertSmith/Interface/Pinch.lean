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

/-- **The radial blow-up is continuous** in the point and the parameter. -/
theorem Continuous.blowup {X : Type*} [TopologicalSpace X] {σ : X → ℝ} {U : X → E}
    (hσ : Continuous σ) (hU : Continuous U) : Continuous fun x => blowup (σ x) (U x) := by
  sorry

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
  sorry

variable [ProperSpace E]

/-- **Pinches depend continuously on their parameters**: `(x, v) ↦ Ψ_{z(x),r(x),s(x)}(v)` is
continuous for continuous `z`, `r > 0` and `s ≥ 0`. At a finite point this is the continuity of
the blow-up; at `∞`, points of large norm are sent to points of large norm or to `∞`. -/
theorem continuous_pinchE {X : Type*} [TopologicalSpace X] {z : X → E} {r s : X → ℝ}
    (hz : Continuous z) (hr : Continuous r) (hs : Continuous s) (hr0 : ∀ x, 0 < r x)
    (hs0 : ∀ x, 0 ≤ s x) :
    Continuous fun q : X × OnePoint E => pinchE (z q.1) (r q.1) (s q.1) q.2 := by
  sorry

/-- The pinch `Ψ_{z,r,s}` as a continuous map, for `r > 0` and `s ≥ 0`. -/
def pinchEMap (z : E) (r s : ℝ) (hr : 0 < r) (hs : 0 ≤ s) : C(OnePoint E, OnePoint E) where
  toFun := pinchE z r s
  continuous_toFun := sorry

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

/-- **Ball paths** (05:495-503): in a connected open `W ⊆ E`, two closed balls in `W` are joined by
a path of centres and radii whose radii stay positive and whose closed balls all lie in one compact
`K ⊆ W`. Join the centres by a path in `W`; its compact image has a closed `δ`-neighbourhood in `W`;
shrink the first radius to `ρ = min δ r₀ r₁`, move the centre along the path with radius `ρ`, and
enlarge the radius to `r₁`. (The radius is not taken to be the distance to `E ∖ W`, which is `0`
when `W = E`.) -/
theorem exists_ballPath {W : Set E} (hW : IsOpen W) (hconn : IsConnected W)
    {z₀ z₁ : E} {r₀ r₁ : ℝ} (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) (h₀ : closedBall z₀ r₀ ⊆ W)
    (h₁ : closedBall z₁ r₁ ⊆ W) :
    ∃ (γ : Path (z₀, r₀) (z₁, r₁)) (K : Set E), IsCompact K ∧ K ⊆ W ∧
      ∀ t, 0 < (γ t).2 ∧ closedBall (γ t).1 (γ t).2 ⊆ K := by
  have hz₀ : z₀ ∈ W := h₀ (mem_closedBall_self hr₀.le)
  have hz₁ : z₁ ∈ W := h₁ (mem_closedBall_self hr₁.le)
  have hJ := (hW.isConnected_iff_isPathConnected.1 hconn).joinedIn z₀ hz₀ z₁ hz₁
  set c := hJ.somePath
  have hcW : range c ⊆ W := by
    rintro _ ⟨t, rfl⟩
    exact hJ.somePath_mem t
  obtain ⟨δ, hδ, hδW⟩ := (isCompact_range c.continuous).exists_cthickening_subset_open hW hcW
  set ρ := min δ (min r₀ r₁)
  have hρ : 0 < ρ := lt_min hδ (lt_min hr₀ hr₁)
  have hρδ : ρ ≤ δ := min_le_left _ _
  have hρ₀ : ρ ≤ r₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hρ₁ : ρ ≤ r₁ := (min_le_right _ _).trans (min_le_right _ _)
  set K := closedBall z₀ r₀ ∪ cthickening δ (range c) ∪ closedBall z₁ r₁
  have hK : IsCompact K :=
    ((isCompact_closedBall _ _).union (isCompact_range c.continuous).cthickening).union
      (isCompact_closedBall _ _)
  have hKW : K ⊆ W := union_subset (union_subset h₀ hδW) h₁
  -- Shrink, move, enlarge.
  let γ₁ : Path (z₀, r₀) (z₀, ρ) :=
    { toFun := fun t => (z₀, (1 - t) * r₀ + t * ρ)
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp }
  let γ₂ : Path (z₀, ρ) (z₁, ρ) :=
    { toFun := fun t => (c t, ρ)
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp }
  let γ₃ : Path (z₁, ρ) (z₁, r₁) :=
    { toFun := fun t => (z₁, (1 - t) * ρ + t * r₁)
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp }
  refine ⟨γ₁.trans (γ₂.trans γ₃), K, hK, hKW, fun t => ?_⟩
  have hmem : (γ₁.trans (γ₂.trans γ₃)) t ∈ range (γ₁.trans (γ₂.trans γ₃)) := mem_range_self t
  rw [Path.trans_range, Path.trans_range] at hmem
  have h01 : ∀ s : unitInterval, (0 : ℝ) ≤ s ∧ (s : ℝ) ≤ 1 := fun s => ⟨s.2.1, s.2.2⟩
  rcases hmem with ⟨s, hs⟩ | ⟨s, hs⟩ | ⟨s, hs⟩
  · rw [← hs]
    obtain ⟨hs0, hs1⟩ := h01 s
    change 0 < (1 - (s : ℝ)) * r₀ + s * ρ ∧ closedBall z₀ ((1 - (s : ℝ)) * r₀ + s * ρ) ⊆ K
    refine ⟨by nlinarith, fun v hv => Or.inl (Or.inl (closedBall_subset_closedBall ?_ hv))⟩
    nlinarith
  · rw [← hs]
    refine ⟨hρ, fun v hv => Or.inl (Or.inr ?_)⟩
    exact cthickening_mono hρδ _ (closedBall_subset_cthickening (mem_range_self s) ρ hv)
  · rw [← hs]
    obtain ⟨hs0, hs1⟩ := h01 s
    change 0 < (1 - (s : ℝ)) * ρ + s * r₁ ∧ closedBall z₁ ((1 - (s : ℝ)) * ρ + s * r₁) ⊆ K
    refine ⟨by nlinarith, fun v hv => Or.inr (closedBall_subset_closedBall ?_ hv)⟩
    nlinarith

end Blowup

namespace LocalAction

variable {p : ℕ} [Fact p.Prime] {k : ℕ} (A : LocalAction p k)

/-- The pinch on `W⁺` as a function: `∞ ↦ ξ = sphereEquiv ∞` and `w ↦ sphereEquiv (Ψ_{z,r,1} w)`. -/
def pinchFun (z : A.E) (r : ℝ) (w : OnePoint A.W) : Sphere k :=
  w.elim (A.sphereEquiv ∞) fun w => A.sphereEquiv (pinchE z r 1 (w : A.E))

/-- **Families of pinches are continuous** when their radii are positive and their closed balls
lie in one compact subset of `W`: off that compact set they are constant `ξ` (05:501-504). -/
theorem continuous_pinchFun {X : Type*} [TopologicalSpace X] {z : X → A.E} {r : X → ℝ}
    (hz : Continuous z) (hr : Continuous r) (hr0 : ∀ x, 0 < r x) {K : Set A.E}
    (hK : IsCompact K) (hKW : K ⊆ A.W) (hball : ∀ x, closedBall (z x) (r x) ⊆ K) :
    Continuous fun q : X × OnePoint A.W => A.pinchFun (z q.1) (r q.1) q.2 := by
  sorry

/-- **The pinch** `P_{z,r}` on `W⁺`, for `r > 0` and `B̄(z, r) ⊆ W` (05:156-160). -/
def pinch (z : A.E) (r : ℝ) (hr : 0 < r) (hzr : closedBall z r ⊆ A.W) :
    C(OnePoint A.W, Sphere k) where
  toFun := A.pinchFun z r
  continuous_toFun := sorry

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
