import HilbertSmith.Interface.ChartReduction
import HilbertSmith.Interface.LocalInputs

/-!
# The orientation facts of §5

The three facts about orientation preservation that OpenAI's §5 uses, for the concrete predicate
`LocalAction.OrientationPreserving` (local maps homotopic to the identity's), proved without
degrees or homology.

* `LocalAction.exists_orientationPreserving_restrict`: on a connected `W`, some open subgroup
  `p^j ℤ_[p]` acts preserving orientation. OpenAI argues (05:68-70) that every homeomorphism of the
  connected `O` preserves or reverses the orientation, so every square preserves it, and replaces
  `H` by `2H`; that dichotomy needs degree theory. **Departure** (decision 2 of the lead's B-M4
  brief): the open subgroup comes from continuity of the action at `0` instead, the device of
  05:53-55. Near `0`, the local map at one fixed `(x₀, ε₀)` stays within `ε₀/2` of `v ↦ ε₀ v` on the
  sphere of radius `1/2`, so a straight line joins them (`exists_padicSubgroup_localMap`); and on a
  connected `W` the homotopy class of a local map does not depend on `(x, ε)`
  (`localMap_homotopic_of_admissible`, along the ball paths of `exists_ballPath`).
* `LocalAction.orientationPreserving_stabilize`: with the product orientation on `W × ℝ^m` and the
  trivial action on `ℝ^m`, the action still preserves orientation (05:75-80). The local map of the
  product is `(v₁, v₂) ↦ (ℓ(v₁), εv₂)`, where `ℓ` vanishes only at `0`; a homotopy of `ℓ` on the
  punctured ball is coned off to the whole ball by `v₁ ↦ ‖v₁‖ • h(v₁)/‖h(v₁)‖`.
* `LocalAction.orientationPreserving_restrict` (in `Orientation.lean`): persistence under the
  replacements of Lemma 5.3 (05:181-182).

Together: `HilbertSmith.Interface.orientation : Orientation LocalAction.OrientationPreserving`.
-/

namespace HilbertSmith.Interface

open Topology Set Metric Filter
open scoped Classical

noncomputable section

section Straight

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Straight-line homotopy in `E ∖ {0}`**: maps `f₀, f₁` into `E ∖ {0}` with
`‖f₀ x − f₁ x‖ < ‖f₁ x‖` everywhere are homotopic, since the segment from `f₀ x` to `f₁ x`
misses `0`. -/
theorem homotopic_of_norm_sub_lt {X : Type*} [TopologicalSpace X]
    (f₀ f₁ : C(X, ({0}ᶜ : Set E))) (h : ∀ x, ‖(f₀ x : E) - f₁ x‖ < ‖(f₁ x : E)‖) :
    f₀.Homotopic f₁ := by
  have hne : ∀ (t : unitInterval) (x : X),
      (1 - (t : ℝ)) • (f₀ x : E) + (t : ℝ) • (f₁ x : E) ≠ 0 := by
    intro t x h0
    have heq : (1 - (t : ℝ)) • (f₀ x : E) + (t : ℝ) • (f₁ x : E) =
        (f₁ x : E) + (1 - (t : ℝ)) • ((f₀ x : E) - f₁ x) := by
      rw [smul_sub, sub_smul, one_smul, sub_smul, one_smul]; abel
    have h1 : ‖(1 - (t : ℝ)) • ((f₀ x : E) - f₁ x)‖ ≤ ‖(f₀ x : E) - f₁ x‖ := by
      rw [norm_smul, Real.norm_of_nonneg (by linarith [t.2.2])]
      exact mul_le_of_le_one_left (norm_nonneg _) (by linarith [t.2.1])
    have h2 := norm_sub_norm_le (f₁ x : E) (-((1 - (t : ℝ)) • ((f₀ x : E) - f₁ x)))
    rw [heq] at h0
    rw [sub_neg_eq_add, h0, norm_zero, norm_neg] at h2
    linarith [h x]
  exact ⟨{ toFun := fun q => ⟨(1 - (q.1 : ℝ)) • (f₀ q.2 : E) + (q.1 : ℝ) • (f₁ q.2 : E),
              hne q.1 q.2⟩
           continuous_toFun := by fun_prop
           map_zero_left := fun x => Subtype.ext (by simp)
           map_one_left := fun x => Subtype.ext (by simp) }⟩

/-- `w ↦ w / ‖w‖`. -/
def nrm (w : E) : E := ‖w‖⁻¹ • w

theorem norm_nrm_le (w : E) : ‖nrm w‖ ≤ 1 := by
  rw [nrm, norm_smul, norm_inv, norm_norm]
  rcases eq_or_ne ‖w‖ 0 with h | h
  · rw [h, inv_zero, zero_mul]; exact zero_le_one
  · rw [inv_mul_cancel₀ h]

theorem nrm_ne_zero {w : E} (hw : w ≠ 0) : nrm w ≠ 0 :=
  smul_ne_zero (inv_ne_zero (norm_ne_zero_iff.2 hw)) hw

theorem continuousOn_nrm : ContinuousOn (nrm : E → E) {0}ᶜ :=
  ((continuous_norm.continuousOn.inv₀ fun _ hw => norm_ne_zero_iff.2 hw).smul continuousOn_id)

/-- **Extension by `0` of `ν • ψ`**: if `ψ` is continuous and bounded by `1` on an open set
`{P}`, and the continuous `ν` vanishes off it, then `y ↦ ν y • ψ y` on `{P}`, `0` elsewhere, is
continuous. -/
theorem continuous_dite_smul {Y : Type*} [TopologicalSpace Y] {P : Y → Prop}
    [∀ y, Decidable (P y)] (hP : IsOpen {y | P y}) {ν : Y → ℝ} (hν : Continuous ν)
    (hν0 : ∀ y, ¬ P y → ν y = 0)
    {ψ : {y // P y} → E} (hψ : Continuous ψ) (hψ1 : ∀ u, ‖ψ u‖ ≤ 1) :
    Continuous fun y => if h : P y then ν y • ψ ⟨y, h⟩ else 0 := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : P y
  · have he : IsOpenEmbedding (Subtype.val : {y // P y} → Y) := hP.isOpenEmbedding_subtypeVal
    refine (he.continuousAt_iff (x := ⟨y, hy⟩)).1 ?_
    have : (fun y => if h : P y then ν y • ψ ⟨y, h⟩ else 0) ∘ Subtype.val =
        fun u : {y // P y} => ν u • ψ u := funext fun u => by simp [u.2]
    rw [this]
    exact ((hν.comp continuous_subtype_val).smul hψ).continuousAt
  · show Tendsto _ _ (𝓝 _)
    simp only [hy, ↓reduceDIte]
    refine squeeze_zero_norm (a := fun z => |ν z|) (fun z => ?_) ?_
    · by_cases hz : P z
      · simp only [hz, ↓reduceDIte, norm_smul, Real.norm_eq_abs]
        exact mul_le_of_le_one_right (abs_nonneg _) (hψ1 _)
      · simp only [hz, ↓reduceDIte, norm_zero]; exact abs_nonneg _
    · simpa [hν0 y hy] using (hν.abs.tendsto y)

/-- **The cone of `f`** on the open unit ball: `v ↦ ‖v‖ • f(v)/‖f(v)‖`, and `0` at `0`. It has
norm `‖v‖` where `f(v) ≠ 0`, so it is continuous at `0`. -/
def cone (f : ball (0 : E) 1 → E) (v : ball (0 : E) 1) : E :=
  if _h : (v : E) ≠ 0 then ‖(v : E)‖ • nrm (f v) else 0

theorem continuous_cone {f : ball (0 : E) 1 → E} (hf : Continuous f)
    (hf0 : ∀ v : ball (0 : E) 1, (v : E) ≠ 0 → f v ≠ 0) : Continuous (cone f) :=
  continuous_dite_smul (P := fun v : ball (0 : E) 1 => (v : E) ≠ 0)
    (isOpen_ne_fun continuous_subtype_val continuous_const)
    (continuous_norm.comp continuous_subtype_val)
    (fun v hv => by rw [not_not] at hv; simp [hv]) (ψ := fun u => nrm (f u.1))
    (continuousOn_nrm.comp_continuous (hf.comp continuous_subtype_val) fun u => hf0 u.1 u.2)
    fun u => norm_nrm_le _

theorem cone_of_ne {f : ball (0 : E) 1 → E} {v : ball (0 : E) 1} (hv : (v : E) ≠ 0) :
    cone f v = ‖(v : E)‖ • nrm (f v) := by
  simp [cone, hv]

theorem cone_ne_zero {f : ball (0 : E) 1 → E} {v : ball (0 : E) 1} (hv : (v : E) ≠ 0)
    (hf : f v ≠ 0) : cone f v ≠ 0 := by
  rw [cone_of_ne hv]
  exact smul_ne_zero (norm_ne_zero_iff.2 hv) (nrm_ne_zero hf)

/-- The restriction of `f`, defined on the open unit ball and vanishing only at `0`, to a map from
the punctured ball to `E ∖ {0}`. -/
def restrictPB (f : ball (0 : E) 1 → E) (hf : Continuous f)
    (hf0 : ∀ v : ball (0 : E) 1, (v : E) ≠ 0 → f v ≠ 0) :
    C(puncturedBall E, ({0}ᶜ : Set E)) where
  toFun v := ⟨f ⟨v, v.2.1⟩, hf0 _ v.2.2⟩
  continuous_toFun :=
    (hf.comp (continuous_subtype_val.subtype_mk fun v : puncturedBall E => v.2.1)).subtype_mk _

/-- A point of the punctured ball, as a point of the ball. -/
def toBall (v : puncturedBall E) : ball (0 : E) 1 := ⟨v, v.2.1⟩

omit [NormedSpace ℝ E] in
theorem continuous_toBall : Continuous (toBall : puncturedBall E → ball (0 : E) 1) :=
  continuous_subtype_val.subtype_mk _

section Product

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The first coordinate of a point of the unit ball of `E × F`, in the unit ball of `E`. -/
def ballFst (v : ball (0 : E × F) 1) : ball (0 : E) 1 :=
  ⟨(v : E × F).1, mem_ball_zero_iff.2 ((norm_fst_le _).trans_lt (mem_ball_zero_iff.1 v.2))⟩

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem continuous_ballFst : Continuous (ballFst : ball (0 : E × F) 1 → ball (0 : E) 1) :=
  (continuous_fst.comp continuous_subtype_val).subtype_mk _

omit [NormedSpace ℝ E] in
/-- For `v ≠ 0` in `E × F` and `ε > 0`, the pair `(a, εv₂)` is nonzero as soon as `a ≠ 0` whenever
`v₁ ≠ 0`. -/
theorem pair_ne_zero (v : puncturedBall (E × F)) {a : E} (ha : (v : E × F).1 ≠ 0 → a ≠ 0)
    {ε : ℝ} (hε : 0 < ε) : ((a, ε • (v : E × F).2) : E × F) ≠ 0 := by
  intro h0
  rw [Prod.mk_eq_zero] at h0
  by_cases h1 : (v : E × F).1 = 0
  · have h2 : (v : E × F).2 = 0 := (smul_eq_zero.1 h0.2).resolve_left hε.ne'
    exact v.2.2 (Prod.ext h1 h2)
  · exact ha h1 h0.1

/-- **The map `(v₁, v₂) ↦ (φ(v₁), εv₂)`** on the punctured ball of `E × F`, for `φ` vanishing only
at `0`: the shape of the local maps of a stabilized action. -/
def stabMap (φ : ball (0 : E) 1 → E) (hφ : Continuous φ)
    (hφ0 : ∀ v : ball (0 : E) 1, (v : E) ≠ 0 → φ v ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    C(puncturedBall (E × F), ({0}ᶜ : Set (E × F))) where
  toFun v := ⟨(φ (ballFst (toBall v)), ε • (v : E × F).2),
    pair_ne_zero v (hφ0 (ballFst (toBall v))) hε⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.prodMk ?_ ?_) _
    · exact hφ.comp (continuous_ballFst.comp continuous_toBall)
    · exact continuous_const.smul (continuous_snd.comp continuous_subtype_val)

theorem combo_ne_zero {a : E} (ha : a ≠ 0) {c : ℝ} (hc : 0 < c) (t : unitInterval) :
    (1 - (t : ℝ)) • a + (t : ℝ) • (c • a) ≠ 0 := by
  rw [smul_smul, ← add_smul]
  refine smul_ne_zero ?_ ha
  rcases eq_or_lt_of_le t.2.2 with h | h
  · rw [h]; simp [hc.ne']
  · nlinarith [mul_nonneg t.2.1 hc.le]

/-- **First stage**: `(φ(v₁), εv₂)` is homotopic to `(cone φ (v₁), εv₂)` along straight lines,
since `cone φ (v₁)` is a positive multiple of `φ(v₁)` for `v₁ ≠ 0`, and both vanish at `v₁ = 0`. -/
theorem stabMap_homotopic_cone (φ : ball (0 : E) 1 → E) (hφ : Continuous φ)
    (hφ0 : ∀ v : ball (0 : E) 1, (v : E) ≠ 0 → φ v ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    (stabMap (F := F) φ hφ hφ0 hε).Homotopic (stabMap (F := F) (cone φ) (continuous_cone hφ hφ0)
      (fun v hv => cone_ne_zero hv (hφ0 v hv)) hε) := by
  have hc : ∀ w : ball (0 : E) 1, (w : E) ≠ 0 →
      cone φ w = (‖(w : E)‖ * ‖φ w‖⁻¹) • φ w := fun w hw => by
    rw [cone_of_ne hw, nrm, smul_smul, mul_comm]
  have hpos : ∀ w : ball (0 : E) 1, (w : E) ≠ 0 → 0 < ‖(w : E)‖ * ‖φ w‖⁻¹ := fun w hw =>
    mul_pos (norm_pos_iff.2 hw) (inv_pos.2 (norm_pos_iff.2 (hφ0 w hw)))
  have hw : Continuous fun v : puncturedBall (E × F) => ballFst (toBall v) :=
    continuous_ballFst.comp continuous_toBall
  exact ⟨{ toFun := fun q => ⟨((1 - (q.1 : ℝ)) • φ (ballFst (toBall q.2)) +
              (q.1 : ℝ) • cone φ (ballFst (toBall q.2)), ε • (q.2 : E × F).2),
              pair_ne_zero q.2 (fun h1 => by
                rw [hc _ h1]
                exact combo_ne_zero (hφ0 _ h1) (hpos _ h1) q.1) hε⟩
           continuous_toFun := by
             refine Continuous.subtype_mk (Continuous.prodMk ?_ ?_) _
             · exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
                 (hφ.comp (hw.comp continuous_snd))).add
                 ((continuous_subtype_val.comp continuous_fst).smul
                 ((continuous_cone hφ hφ0).comp (hw.comp continuous_snd)))
             · exact continuous_const.smul (continuous_snd.comp
                 (continuous_subtype_val.comp continuous_snd))
           map_zero_left := fun v => Subtype.ext (by simp [stabMap])
           map_one_left := fun v => Subtype.ext (by simp [stabMap]) }⟩

/-- **Second stage**: a homotopy between the restrictions of `f₀` and `f₁` to the punctured ball
cones off to a homotopy between `(cone f₀ (v₁), εv₂)` and `(cone f₁ (v₁), εv₂)`: on `v₁ ≠ 0` use
`‖v₁‖ • h(v₁)/‖h(v₁)‖`, and `0` at `v₁ = 0` (continuous, since its norm is `‖v₁‖`). -/
theorem stabMap_cone_homotopic (f₀ f₁ : ball (0 : E) 1 → E) (hf₀ : Continuous f₀)
    (hf₁ : Continuous f₁) (hf₀0 : ∀ v : ball (0 : E) 1, (v : E) ≠ 0 → f₀ v ≠ 0)
    (hf₁0 : ∀ v : ball (0 : E) 1, (v : E) ≠ 0 → f₁ v ≠ 0) {ε : ℝ} (hε : 0 < ε)
    (H : (restrictPB f₀ hf₀ hf₀0).Homotopic (restrictPB f₁ hf₁ hf₁0)) :
    (stabMap (F := F) (cone f₀) (continuous_cone hf₀ hf₀0)
      (fun v hv => cone_ne_zero hv (hf₀0 v hv)) hε).Homotopic
    (stabMap (F := F) (cone f₁) (continuous_cone hf₁ hf₁0)
      (fun v hv => cone_ne_zero hv (hf₁0 v hv)) hε) := by
  obtain ⟨H⟩ := H
  let K : unitInterval × ball (0 : E) 1 → E := fun q =>
    if h : (q.2 : E) ≠ 0 then ‖(q.2 : E)‖ • nrm (H (q.1, ⟨q.2, q.2.2, h⟩) : E) else 0
  have hK : Continuous K := by
    refine continuous_dite_smul (P := fun q : unitInterval × ball (0 : E) 1 => (q.2 : E) ≠ 0)
      (isOpen_ne_fun (continuous_subtype_val.comp continuous_snd) continuous_const)
      (continuous_norm.comp (continuous_subtype_val.comp continuous_snd))
      (fun q hq => by rw [not_not] at hq; simp [hq])
      (ψ := fun u => nrm (H (u.1.1, ⟨u.1.2, u.1.2.2, u.2⟩) : E)) ?_ fun u => norm_nrm_le _
    refine continuousOn_nrm.comp_continuous (continuous_subtype_val.comp (H.continuous.comp ?_))
      fun u => (H _).2
    exact (continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)).subtype_mk _)
  have hK0 : ∀ q : unitInterval × ball (0 : E) 1, (q.2 : E) ≠ 0 → K q ≠ 0 := fun q hq => by
    simp only [K]
    split_ifs
    exact smul_ne_zero (norm_ne_zero_iff.2 hq) (nrm_ne_zero (H _).2)
  have hKz : ∀ q : unitInterval × ball (0 : E) 1, (q.2 : E) = 0 → K q = 0 := fun q hq => by
    simp only [K]
    split_ifs with h
    · exact absurd hq h
    · rfl
  have hKnz : ∀ (q : unitInterval × ball (0 : E) 1) (hq : (q.2 : E) ≠ 0),
      K q = ‖(q.2 : E)‖ • nrm (H (q.1, ⟨q.2, q.2.2, hq⟩) : E) := fun q hq => by
    simp only [K]
    split_ifs
    rfl
  have hw : Continuous fun v : puncturedBall (E × F) => ballFst (toBall v) :=
    continuous_ballFst.comp continuous_toBall
  refine ⟨{ toFun := fun q => ⟨(K (q.1, ballFst (toBall q.2)), ε • (q.2 : E × F).2),
              pair_ne_zero q.2 (fun h1 => hK0 _ h1) hε⟩
            continuous_toFun := by
              refine Continuous.subtype_mk (Continuous.prodMk ?_ ?_) _
              · exact hK.comp (continuous_fst.prodMk (hw.comp continuous_snd))
              · exact continuous_const.smul (continuous_snd.comp
                  (continuous_subtype_val.comp continuous_snd))
            map_zero_left := fun v => ?_
            map_one_left := fun v => ?_ }⟩
  · refine Subtype.ext (Prod.ext ?_ rfl)
    change K (0, ballFst (toBall v)) = cone f₀ (ballFst (toBall v))
    by_cases hv : ((ballFst (toBall v) : ball (0 : E) 1) : E) = 0
    · rw [hKz _ hv]
      simp [cone, hv]
    · rw [hKnz _ hv, H.apply_zero, cone_of_ne hv]
      rfl
  · refine Subtype.ext (Prod.ext ?_ rfl)
    change K (1, ballFst (toBall v)) = cone f₁ (ballFst (toBall v))
    by_cases hv : ((ballFst (toBall v) : ball (0 : E) 1) : E) = 0
    · rw [hKz _ hv]
      simp [cone, hv]
    · rw [hKnz _ hv, H.apply_one, cone_of_ne hv]
      rfl

end Product

end Straight

namespace LocalAction

variable {p : ℕ} [Fact p.Prime] {k : ℕ} (A : LocalAction p k)

/-! ### Families of local maps -/

/-- Local vectors depend continuously on `g`, `x`, `ε` and `v`. -/
theorem continuous_localVec_family {X : Type*} [TopologicalSpace X] {g : X → ℤ_[p]}
    {x : X → A.E} {ε : X → ℝ} (hg : Continuous g) (hx : Continuous x) (hε : Continuous ε)
    (h : ∀ t, A.Admissible (x t) (ε t)) :
    Continuous fun q : X × ball (0 : A.E) 1 => A.localVec (g q.1) (h q.1) q.2 := by
  have h1 : Continuous fun q : X × ball (0 : A.E) 1 => A.ballPoint (h q.1) q.2 :=
    ((hx.comp continuous_fst).add ((hε.comp continuous_fst).smul
      (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  have h2 : Continuous fun q : X × ball (0 : A.E) 1 => (⟨x q.1, (h q.1).mem⟩ : A.W) :=
    (hx.comp continuous_fst).subtype_mk _
  exact (continuous_subtype_val.comp ((hg.comp continuous_fst).vadd h1)).sub
    (continuous_subtype_val.comp ((hg.comp continuous_fst).vadd h2))

theorem localVec_congr (g : ℤ_[p]) {x x' : A.E} {ε ε' : ℝ} (hx : x = x') (hε : ε = ε')
    (h : A.Admissible x ε) (h' : A.Admissible x' ε') (v : ball (0 : A.E) 1) :
    A.localVec g h v = A.localVec g h' v := by
  subst hx hε; rfl

/-- **Local maps along a path of admissible pairs are homotopic.** -/
theorem localMap_homotopic_of_path (g : ℤ_[p]) {x : unitInterval → A.E} {ε : unitInterval → ℝ}
    (hx : Continuous x) (hε : Continuous ε) (h : ∀ t, A.Admissible (x t) (ε t))
    {x₀ x₁ : A.E} {ε₀ ε₁ : ℝ} (h₀ : A.Admissible x₀ ε₀) (h₁ : A.Admissible x₁ ε₁)
    (e₀ : x 0 = x₀) (f₀ : ε 0 = ε₀) (e₁ : x 1 = x₁) (f₁ : ε 1 = ε₁) :
    (A.localMap g h₀).Homotopic (A.localMap g h₁) := by
  have hc := A.continuous_localVec_family (g := fun _ => g) (x := x) (ε := ε) continuous_const hx
    hε h
  exact ⟨{ toFun := fun q => ⟨A.localVec g (h q.1) ⟨q.2, q.2.2.1⟩, fun h0 =>
              q.2.2.2 ((A.localVec_eq_zero_iff g (h q.1) _).1 h0)⟩
           continuous_toFun := (hc.comp (continuous_fst.prodMk
              ((continuous_subtype_val.comp continuous_snd).subtype_mk _))).subtype_mk _
           map_zero_left := fun v => Subtype.ext (A.localVec_congr g e₀ f₀ (h 0) h₀ _)
           map_one_left := fun v => Subtype.ext (A.localVec_congr g e₁ f₁ (h 1) h₁ _) }⟩

/-- Halving the radius does not change the homotopy class of a local map. -/
theorem localMap_homotopic_half (g : ℤ_[p]) {x : A.E} {ε : ℝ} (h : A.Admissible x ε)
    (h' : A.Admissible x (ε / 2)) : (A.localMap g h).Homotopic (A.localMap g h') := by
  have hp : ∀ t : unitInterval, A.Admissible x (ε - t * (ε / 2)) := fun t =>
    ⟨by nlinarith [t.2.2, h.1], (ball_subset_ball (by nlinarith [t.2.1, h.1])).trans h.2⟩
  exact A.localMap_homotopic_of_path g (x := fun _ => x) (ε := fun t => ε - t * (ε / 2))
    continuous_const (by fun_prop) hp h h' rfl (by simp) rfl (by simp; ring)

/-- **On a connected `W`, the homotopy class of a local map does not depend on `(x, ε)`**: halve
both radii, so that the closed balls lie in `W`, and join them by a ball path
(`exists_ballPath`). -/
theorem localMap_homotopic_of_admissible (hconn : IsConnected A.W) (g : ℤ_[p]) {x₀ x₁ : A.E}
    {ε₀ ε₁ : ℝ} (h₀ : A.Admissible x₀ ε₀) (h₁ : A.Admissible x₁ ε₁) :
    (A.localMap g h₀).Homotopic (A.localMap g h₁) := by
  have half : ∀ {x : A.E} {ε : ℝ}, A.Admissible x ε →
      A.Admissible x (ε / 2) ∧ closedBall x (ε / 2) ⊆ A.W := fun h =>
    ⟨⟨half_pos h.1, (ball_subset_ball (half_le_self h.1.le)).trans h.2⟩,
      (closedBall_subset_ball (half_lt_self h.1)).trans h.2⟩
  obtain ⟨h₀', hc₀⟩ := half h₀
  obtain ⟨h₁', hc₁⟩ := half h₁
  obtain ⟨γ, K, -, hKW, hγ⟩ :=
    exists_ballPath A.isOpen hconn (half_pos h₀.1) (half_pos h₁.1) hc₀ hc₁
  have hp : ∀ t, A.Admissible (γ t).1 (γ t).2 := fun t =>
    ⟨(hγ t).1, ball_subset_closedBall.trans ((hγ t).2.trans hKW)⟩
  have hmid := A.localMap_homotopic_of_path g (x := fun t => (γ t).1) (ε := fun t => (γ t).2)
    (continuous_fst.comp γ.continuous) (continuous_snd.comp γ.continuous) hp h₀' h₁'
    (by simp) (by simp) (by simp) (by simp)
  exact (A.localMap_homotopic_half g h₀ h₀').trans
    (hmid.trans (A.localMap_homotopic_half g h₁ h₁').symm)

/-! ### Near `0` -/

theorem smul_mem_puncturedBall (t : unitInterval) (v : puncturedBall A.E) :
    ((1 - (t : ℝ)) + t * (2 * ‖(v : A.E)‖)⁻¹) • (v : A.E) ∈ puncturedBall A.E := by
  have hv0 : (v : A.E) ≠ 0 := v.2.2
  have hv1 : ‖(v : A.E)‖ < 1 := mem_ball_zero_iff.1 v.2.1
  have hn : 0 < ‖(v : A.E)‖ := norm_pos_iff.2 hv0
  have ht0 := t.2.1
  have ht1 := t.2.2
  have hc : 0 < (1 - (t : ℝ)) + t * (2 * ‖(v : A.E)‖)⁻¹ := by
    rcases eq_or_lt_of_le ht1 with h | h
    · rw [h]; simp only [sub_self, zero_add, one_mul]; positivity
    · have : 0 ≤ (t : ℝ) * (2 * ‖(v : A.E)‖)⁻¹ := by positivity
      linarith
  refine ⟨mem_ball_zero_iff.2 ?_, smul_ne_zero hc.ne' hv0⟩
  rw [norm_smul, Real.norm_of_nonneg hc.le]
  have he : ((1 - (t : ℝ)) + t * (2 * ‖(v : A.E)‖)⁻¹) * ‖(v : A.E)‖ =
      (1 - t) * ‖(v : A.E)‖ + t / 2 := by
    field_simp
  rw [he]
  nlinarith

theorem retractHalf_mem (v : puncturedBall A.E) :
    (2 * ‖(v : A.E)‖)⁻¹ • (v : A.E) ∈ puncturedBall A.E := by
  have := A.smul_mem_puncturedBall 1 v
  rwa [show (1 - ((1 : unitInterval) : ℝ)) + ((1 : unitInterval) : ℝ) * (2 * ‖(v : A.E)‖)⁻¹ =
    (2 * ‖(v : A.E)‖)⁻¹ by simp] at this

/-- The radial retraction `v ↦ v/(2‖v‖)` of the punctured ball onto the sphere of radius `1/2`. -/
def retractHalf : C(puncturedBall A.E, puncturedBall A.E) where
  toFun v := ⟨(2 * ‖(v : A.E)‖)⁻¹ • (v : A.E), A.retractHalf_mem v⟩
  continuous_toFun := (((continuous_const.mul (continuous_norm.comp continuous_subtype_val)).inv₀
    fun v => mul_ne_zero two_ne_zero (norm_ne_zero_iff.2 v.2.2)).smul
    continuous_subtype_val).subtype_mk _

theorem norm_retractHalf (v : puncturedBall A.E) : ‖(A.retractHalf v : A.E)‖ = 1 / 2 := by
  have hn : ‖(v : A.E)‖ ≠ 0 := norm_ne_zero_iff.2 v.2.2
  change ‖(2 * ‖(v : A.E)‖)⁻¹ • (v : A.E)‖ = 1 / 2
  rw [norm_smul, norm_inv, norm_mul, Real.norm_two, norm_norm]
  field_simp

/-- The identity of the punctured ball is homotopic to the retraction onto radius `1/2`. -/
theorem id_homotopic_retractHalf : (ContinuousMap.id (puncturedBall A.E)).Homotopic A.retractHalf :=
  ⟨{ toFun := fun q => ⟨((1 - (q.1 : ℝ)) + q.1 * (2 * ‖(q.2 : A.E)‖)⁻¹) • (q.2 : A.E),
        A.smul_mem_puncturedBall q.1 q.2⟩
     continuous_toFun := by
       refine Continuous.subtype_mk (Continuous.smul ?_ (continuous_subtype_val.comp
         continuous_snd)) _
       exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).add
         ((continuous_subtype_val.comp continuous_fst).mul
         ((continuous_const.mul (continuous_norm.comp (continuous_subtype_val.comp
           continuous_snd))).inv₀ fun q => mul_ne_zero two_ne_zero (norm_ne_zero_iff.2 q.2.2.2)))
     map_zero_left := fun v => Subtype.ext (by simp)
     map_one_left := fun v => Subtype.ext (by simp [retractHalf]) }⟩

/-- **Near `0`, local maps at a fixed `(x₀, ε₀)` are homotopic to the identity's** (the device of
05:53-55, continuity of the action at `0`). On the compact sphere of radius `1/2`, the local map of
`g` stays within `ε₀/2` of `v ↦ ε₀ v` for `g` near `0`; the local maps retract radially onto that
sphere, where a straight line in `E ∖ {0}` joins them. -/
theorem exists_padicSubgroup_localMap {x₀ : A.E} {ε₀ : ℝ} (h : A.Admissible x₀ ε₀) :
    ∃ j, ∀ g ∈ padicSubgroup p j, (A.localMap g h).Homotopic (A.localMap 0 h) := by
  set S : Set (ball (0 : A.E) 1) := (↑) ⁻¹' sphere (0 : A.E) (1 / 2)
  have hS : IsCompact S := by
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe,
      inter_eq_right.2 (sphere_subset_ball (by norm_num))]
    exact isCompact_sphere _ _
  have hF : Continuous fun q : ℤ_[p] × ball (0 : A.E) 1 =>
      ‖A.localVec q.1 h q.2 - A.localVec 0 h q.2‖ :=
    ((A.continuous_localVec_family (g := fun g => g) (x := fun _ => x₀) (ε := fun _ => ε₀)
      continuous_id continuous_const continuous_const fun _ => h).sub
      ((A.continuous_localVec 0 h).comp continuous_snd)).norm
  have hev : ∀ᶠ g in 𝓝 (0 : ℤ_[p]), ∀ u ∈ S, ‖A.localVec g h u - A.localVec 0 h u‖ < ε₀ / 2 :=
    hS.eventually_forall_of_forall_eventually fun u _ =>
      hF.continuousAt.eventually (gt_mem_nhds (by simpa using half_pos h.1))
  obtain ⟨t, htU, ht, h0t⟩ := _root_.mem_nhds_iff.1 hev
  obtain ⟨j, hj⟩ := exists_padicSubgroup_subset ht h0t
  refine ⟨j, fun g hg => ?_⟩
  have hgS : ∀ u ∈ S, ‖A.localVec g h u - A.localVec 0 h u‖ < ‖A.localVec 0 h u‖ := by
    intro u hu
    have hb : ‖A.localVec 0 h u‖ = ε₀ / 2 := by
      rw [A.localVec_zero h u, norm_smul, Real.norm_of_nonneg h.1.le,
        mem_sphere_zero_iff_norm.1 hu]
      ring
    rw [hb]
    exact htU (hj hg) u hu
  have hret : ∀ f : C(puncturedBall A.E, ({0}ᶜ : Set A.E)), f.Homotopic (f.comp A.retractHalf) :=
    fun f => by
      have := (ContinuousMap.Homotopic.refl f).comp A.id_homotopic_retractHalf
      rwa [ContinuousMap.comp_id] at this
  refine (hret _).trans ((homotopic_of_norm_sub_lt _ _ fun v => ?_).trans (hret _).symm)
  have hu : (⟨(A.retractHalf v : A.E), (A.retractHalf v).2.1⟩ : ball (0 : A.E) 1) ∈ S :=
    mem_sphere_zero_iff_norm.2 (A.norm_retractHalf v)
  exact hgS _ hu

/-- **On a connected `W`, some open subgroup acts preserving orientation.** Departure from
05:68-72 (decision 2 of the lead's B-M4 brief): the subgroup comes from continuity at `0`
(`exists_padicSubgroup_localMap`) and the independence of `(x, ε)`
(`localMap_homotopic_of_admissible`), not from the preserve-or-reverse dichotomy. -/
theorem exists_orientationPreserving_restrict (hconn : IsConnected A.W) :
    ∃ j, (A.restrict j).OrientationPreserving := by
  obtain ⟨x₀, hx₀⟩ := hconn.nonempty
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.isOpen_iff.1 A.isOpen x₀ hx₀
  have h₀ : A.Admissible x₀ ε₀ := ⟨hε₀, hball⟩
  obtain ⟨j, hj⟩ := A.exists_padicSubgroup_localMap h₀
  refine ⟨j, fun g x ε h => ?_⟩
  change (A.localMap _ h).Homotopic (A.localMap ((p : ℤ_[p]) ^ j * 0) h)
  rw [mul_zero]
  have hmem : (p : ℤ_[p]) ^ j * g ∈ padicSubgroup p j := mem_padicSubgroup.2 (dvd_mul_right _ _)
  exact (A.localMap_homotopic_of_admissible hconn _ h h₀).trans
    ((hj _ hmem).trans (A.localMap_homotopic_of_admissible hconn 0 h₀ h))

/-! ### Stabilization -/

/-- An admissible pair of `W × ℝ^m` gives an admissible pair of `W`: by `ball_prod_same`, the ball
of the product is the product of the balls. -/
theorem admissible_stabilize (d : ℕ) (hd : k ≤ d) {x : A.E × EuclideanSpace ℝ (Fin (d - k))}
    {ε : ℝ} (h : (A.stabilize d hd).Admissible x ε) : A.Admissible x.1 ε := by
  refine ⟨h.1, fun y hy => ?_⟩
  have hmem : ((y, x.2) : A.E × EuclideanSpace ℝ (Fin (d - k))) ∈ ball x ε := by
    rw [mem_ball, Prod.dist_eq, dist_self]
    exact max_lt (mem_ball.1 hy) h.1
  exact (show (y, x.2) ∈ A.W ×ˢ (univ : Set (EuclideanSpace ℝ (Fin (d - k)))) from h.2 hmem).1

/-- **The local vectors of `W × ℝ^m`** are `(ℓ(v₁), εv₂)`, with `ℓ` those of `W`. -/
theorem localVec_stabilize (d : ℕ) (hd : k ≤ d) (g : ℤ_[p])
    {x : A.E × EuclideanSpace ℝ (Fin (d - k))} {ε : ℝ} (h : (A.stabilize d hd).Admissible x ε)
    (v : ball (0 : A.E × EuclideanSpace ℝ (Fin (d - k))) 1) :
    ((A.stabilize d hd).localVec g h v : A.E × EuclideanSpace ℝ (Fin (d - k))) =
      (A.localVec g (A.admissible_stabilize d hd h) (ballFst v),
        ε • (v : A.E × EuclideanSpace ℝ (Fin (d - k))).2) := by
  refine Prod.ext rfl ?_
  change (x.2 + ε • (v : A.E × EuclideanSpace ℝ (Fin (d - k))).2) - x.2 = _
  rw [add_sub_cancel_left]

/-- **Stabilization keeps orientation preservation** (05:75-80): the local maps of `W × ℝ^m` are
`(v₁, v₂) ↦ (ℓ_g(v₁), εv₂)`; straight lines join them to `(cone ℓ_g (v₁), εv₂)`, the cone of a
homotopy `ℓ_g ≃ ℓ_0` joins those for `g` and `0`, and straight lines lead back. -/
theorem orientationPreserving_stabilize (d : ℕ) (hd : k ≤ d) (hA : A.OrientationPreserving) :
    (A.stabilize d hd).OrientationPreserving := by
  intro g x ε h
  have a := A.admissible_stabilize d hd h
  have hne : ∀ g' : ℤ_[p], ∀ v : ball (0 : A.E) 1, (v : A.E) ≠ 0 → A.localVec g' a v ≠ 0 :=
    fun g' v hv => mt (A.localVec_eq_zero_iff g' a v).1 hv
  have e : ∀ g' : ℤ_[p], (A.stabilize d hd).localMap g' h =
      stabMap (A.localVec g' a) (A.continuous_localVec g' a) (hne g') h.1 :=
    fun g' => ContinuousMap.ext fun v => Subtype.ext (A.localVec_stabilize d hd g' h (toBall v))
  have r : ∀ g' : ℤ_[p], A.localMap g' a =
      restrictPB (A.localVec g' a) (A.continuous_localVec g' a) (hne g') := fun g' => rfl
  have H := hA g x.1 ε a
  rw [r, r] at H
  rw [e, e]
  exact (stabMap_homotopic_cone _ _ _ _).trans
    ((stabMap_cone_homotopic _ _ _ _ _ _ _ H).trans (stabMap_homotopic_cone _ _ _ _).symm)

end LocalAction

/-- **The orientation facts of §5** for the concrete predicate
`LocalAction.OrientationPreserving`. -/
theorem orientation : Orientation LocalAction.OrientationPreserving where
  exists_restrict A hconn := A.exists_orientationPreserving_restrict hconn
  restrict A j hA := A.orientationPreserving_restrict j hA
  stabilize A d hd hA := A.orientationPreserving_stabilize d hd hA

end

end HilbertSmith.Interface
