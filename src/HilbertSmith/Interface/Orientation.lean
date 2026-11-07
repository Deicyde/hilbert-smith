import HilbertSmith.Interface.Spaces

/-!
# Orientation preservation by local maps

OpenAI's §5 asks that the action preserve orientation (Proposition 5.1, 05:68-72; after
stabilization, 05:75-80; under the replacements of Lemma 5.3, 05:181-182), and Lemma 6.2's proof
uses it "by naturality of orientation" (06:160-162). Reading that as local homology (`g_*` is the
identity on `H_k(W, W ∖ x) → H_k(W, W ∖ gx)` under the orientation classes) is decision 3 of the
lead's B-M4 brief. This file states orientation preservation concretely, with no homology and no
degree.

For `(x, ε)` with `0 < ε` and the open ball `B(x, ε)` inside `W`, and `g ∈ ℤ_[p]`, the **local
map** of `g` at `(x, ε)` sends a point `v ≠ 0` of the open unit ball to `g(x + εv) − g(x)`, a
nonzero vector since `g` acts injectively. An action **preserves orientation** when, for every
`g` and every such `(x, ε)`, this local map is homotopic, as a map into `E ∖ {0}`, to the local map
of `0`, which is `v ↦ εv`.

This implies the local-homology notion. By excision and translation, both `H_k(W, W ∖ x)` and
`H_k(W, W ∖ gx)` are identified with `H_k(E, E ∖ 0) ≅ H̃_{k−1}(E ∖ 0)`; under these
identifications `g_*` is induced by the local map of `g` at `x`, since the punctured unit ball
includes into `E ∖ 0` as a homotopy equivalence. Homotopic local maps induce equal maps, so a local
map homotopic to `v ↦ εv` gives `g_* = id`.

## Main definitions

* `HilbertSmith.Interface.puncturedBall E`: the open unit ball of `E` without `0`.
* `HilbertSmith.Interface.LocalAction.Admissible`: `0 < ε` and `B(x, ε) ⊆ W`.
* `HilbertSmith.Interface.LocalAction.localMap`: the local map of `g` at `(x, ε)`.
* `HilbertSmith.Interface.LocalAction.OrientationPreserving`: every local map is homotopic to that
  of `0`.

## Main results

* `HilbertSmith.Interface.LocalAction.localMap_zero_apply`: the local map of `0` is `v ↦ εv`.
* `HilbertSmith.Interface.LocalAction.localMap_restrict`: the local maps of `A.restrict j` are those
  of `A` at `p^j g`.
* `HilbertSmith.Interface.LocalAction.orientationPreserving_restrict`: orientation preservation
  persists under the replacements of Lemma 5.3 (05:181-182).
-/

namespace HilbertSmith.Interface

open Topology Set Metric

noncomputable section

/-- The open unit ball of `E` without `0`, the domain of the local maps. -/
def puncturedBall (E : Type*) [NormedAddCommGroup E] : Set E := ball 0 1 \ {0}

namespace LocalAction

variable {p : ℕ} [Fact p.Prime] {k : ℕ} (A : LocalAction p k)

/-- `(x, ε)` is **admissible** when `0 < ε` and the open ball `B(x, ε)` lies in `W`. -/
def Admissible (x : A.E) (ε : ℝ) : Prop := 0 < ε ∧ ball x ε ⊆ A.W

variable {A}

/-- For admissible `(x, ε)` and `‖v‖ < 1`, the point `x + εv` lies in `W`. -/
theorem Admissible.add_smul_mem {x : A.E} {ε : ℝ} (h : A.Admissible x ε) {v : A.E}
    (hv : v ∈ ball (0 : A.E) 1) : x + ε • v ∈ A.W := by
  refine h.2 ?_
  rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg h.1.le]
  rw [mem_ball_zero_iff] at hv
  nlinarith [h.1]

/-- For admissible `(x, ε)`, the centre `x` lies in `W`. -/
theorem Admissible.mem {x : A.E} {ε : ℝ} (h : A.Admissible x ε) : x ∈ A.W :=
  h.2 (mem_ball_self h.1)

variable (A)

/-- The point `x + εv` of `W`, for admissible `(x, ε)` and `‖v‖ < 1`. -/
def ballPoint {x : A.E} {ε : ℝ} (h : A.Admissible x ε) (v : ball (0 : A.E) 1) : A.W :=
  ⟨x + ε • (v : A.E), h.add_smul_mem v.2⟩

theorem continuous_ballPoint {x : A.E} {ε : ℝ} (h : A.Admissible x ε) :
    Continuous (A.ballPoint h) :=
  (continuous_const.add (continuous_const.smul continuous_subtype_val)).subtype_mk _

/-- The vector `g(x + εv) − g(x)`, for `v` in the open unit ball. -/
def localVec (g : ℤ_[p]) {x : A.E} {ε : ℝ} (h : A.Admissible x ε) (v : ball (0 : A.E) 1) : A.E :=
  ((g +ᵥ A.ballPoint h v : A.W) : A.E) - ((g +ᵥ (⟨x, h.mem⟩ : A.W) : A.W) : A.E)

theorem continuous_localVec (g : ℤ_[p]) {x : A.E} {ε : ℝ} (h : A.Admissible x ε) :
    Continuous (A.localVec g h) :=
  (continuous_subtype_val.comp ((continuous_const_vadd g).comp (A.continuous_ballPoint h))).sub
    continuous_const

/-- `g(x + εv) − g(x)` vanishes only at `v = 0`, since `g` acts injectively. -/
theorem localVec_eq_zero_iff (g : ℤ_[p]) {x : A.E} {ε : ℝ} (h : A.Admissible x ε)
    (v : ball (0 : A.E) 1) : A.localVec g h v = 0 ↔ (v : A.E) = 0 := by
  rw [localVec, sub_eq_zero, Subtype.val_inj, vadd_left_cancel_iff, ballPoint,
    Subtype.mk.injEq, add_eq_left, smul_eq_zero, or_iff_right h.1.ne']

/-- For `g = 0`, the vector `g(x + εv) − g(x)` is `εv`. -/
theorem localVec_zero {x : A.E} {ε : ℝ} (h : A.Admissible x ε) (v : ball (0 : A.E) 1) :
    A.localVec 0 h v = ε • (v : A.E) := by
  simp [localVec, ballPoint]

/-- **The local map** of `g` at admissible `(x, ε)`: `v ↦ g(x + εv) − g(x)` from the punctured
unit ball to `E ∖ {0}`. -/
def localMap (g : ℤ_[p]) {x : A.E} {ε : ℝ} (h : A.Admissible x ε) :
    C(puncturedBall A.E, ({0}ᶜ : Set A.E)) where
  toFun v := ⟨A.localVec g h ⟨v, v.2.1⟩, fun h0 =>
    v.2.2 ((A.localVec_eq_zero_iff g h ⟨v, v.2.1⟩).1 h0)⟩
  continuous_toFun := ((A.continuous_localVec g h).comp
    (continuous_subtype_val.subtype_mk fun v : puncturedBall A.E => v.2.1)).subtype_mk _

@[simp] theorem coe_localMap (g : ℤ_[p]) {x : A.E} {ε : ℝ} (h : A.Admissible x ε)
    (v : puncturedBall A.E) : (A.localMap g h v : A.E) = A.localVec g h ⟨v, v.2.1⟩ := rfl

/-- The local map of `0` is `v ↦ εv`. -/
theorem localMap_zero_apply {x : A.E} {ε : ℝ} (h : A.Admissible x ε) (v : puncturedBall A.E) :
    (A.localMap 0 h v : A.E) = ε • (v : A.E) :=
  A.localVec_zero h _

/-- **Orientation preservation**: for every `g` and every admissible `(x, ε)`, the local map of `g`
at `(x, ε)` is homotopic, into `E ∖ {0}`, to that of `0`, which is `v ↦ εv`. -/
def OrientationPreserving : Prop :=
  ∀ (g : ℤ_[p]) (x : A.E) (ε : ℝ) (h : A.Admissible x ε),
    (A.localMap g h).Homotopic (A.localMap 0 h)

/-- The local maps of `A.restrict j` are those of `A` at `p^j g`, since `g` acts on `W` as `p^j g`
(`LocalAction.restrictAct`). -/
theorem localMap_restrict (j : ℕ) (g : ℤ_[p]) {x : A.E} {ε : ℝ} (h : A.Admissible x ε) :
    (A.restrict j).localMap g h = A.localMap ((p : ℤ_[p]) ^ j * g) h :=
  rfl

/-- **Orientation preservation persists when `G` is replaced by an open subgroup** (Lemma 5.3,
"Faithfulness and orientation preservation persist under this replacement", 05:181-182). -/
theorem orientationPreserving_restrict (j : ℕ) (hA : A.OrientationPreserving) :
    (A.restrict j).OrientationPreserving := by
  intro g x ε h
  change (A.localMap _ h).Homotopic (A.localMap ((p : ℤ_[p]) ^ j * 0) h)
  rw [mul_zero]
  exact hA _ x ε h

end LocalAction

end

end HilbertSmith.Interface
