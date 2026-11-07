import HilbertSmith.Interface.Invariant
import HilbertSmith.Interface.Orientation
import HilbertSmith.Interface.Pinch

/-!
# The topology of §5 that the route uses

OpenAI's §5 prepares the local test that §6 consumes. B1 bundled it into one field
`LocalTests.source`; following PLAN §3.2 (change 3) it is split here into its pieces, each a `Prop`
stated as close to OpenAI's text as the formal layer allows, so that each can be proved or kept as
a published input on its own.

Assumed, as the only field of `LocalInputs O`:
* `OrbitNull d δD`: Lemmas 5.4 and 5.5 combined, in the form the proof of Proposition 5.8 uses.

Stated here and proved:
* `Orientation OP`: the facts about orientation preservation that §5 uses, proved for the concrete
  predicate `LocalAction.OrientationPreserving` (local maps homotopic to the identity's) as
  `HilbertSmith.Interface.orientation`.
* `CollapseInput`: Lemma 5.2 (the extended action is continuous; the orbit space is metrizable),
  proved as `HilbertSmith.Interface.collapseInput`.
* `AveragedTest d`: Lemma 5.3 in OpenAI's pinch form (05:148-149), proved as
  `HilbertSmith.Interface.averagedTest`; (5.1) follows (`HilbertSmith.Interface.aqc_homotopic_id`).
* `PinchTransport d`: the pinch transport of the first paragraph of the proof of Proposition 5.8,
  proved as `HilbertSmith.Interface.pinchTransport`.
* `SheetsInput`: what §6 uses of Lemma 5.6, the region `V` and its multiplier `β`, proved as
  `HilbertSmith.Interface.sheetsInput`;
* and, from §6, `SphereBasis d` and `ClosePairBasis d`: the neighbourhood bases of `S^d`
  (06:101-107) and `C_d` (06:355-366), proved as `HilbertSmith.Interface.sphereBasis` and
  `HilbertSmith.Interface.closePairBasis`.

What §6 uses of Proposition 5.1 is not an input either: `HilbertSmith.Interface.chartReductionNoSC`
proves it from `HilbertSmith.NewmanInput`, without second countability, and
`Orientation.exists_restrict` its orientation step. Lemma 5.7 is Deicyde's
`HilbertSmith.homotopyExtension`.

Departures:
* Lemmas 5.4 and 5.5 are stated about rational Čech cohomology, which neither Mathlib nor TauCeti
  has. `OrbitNull` is their composite, which needs no cohomology: if `v ∘ r` is nullhomotopic for
  an orbit map `r`, then `v^*γ_d` vanishes after pulling back, hence vanishes (Lemma 5.4), hence
  some `D_s ∘ v` is nullhomotopic (Lemma 5.5). It splits into the two lemmas once a Čech
  cohomology of compact metrizable spaces is available (accepted in the lead's review of
  2026-11-07, PLAN §3.4 amended).
* Lemma 5.3 is stated in its pinch form, and (5.1) is a theorem (decision 1 of the lead's B-M4
  brief); the pinch maps are `LocalAction.pinch`.
* The orientation step of Proposition 5.1 is proved by continuity of the action at `0`, not by the
  preserve-or-reverse dichotomy, which needs degree theory (decision 2 of the lead's B-M4 brief;
  `Orientation.exists_restrict`).

Scope and non-vacuity. `OrbitNull` is stated for odd `d ≥ 3`, and is true when the maps `D k` of
the interface really have degree `k`; it quantifies over every compact metrizable space with an
action, and assumes what its lemmas need.
-/

namespace HilbertSmith.Interface

open Topology Set

/-- **What §5 uses about orientation preservation**, for a predicate `OP` on local actions. It
holds for `LocalAction.OrientationPreserving` (`HilbertSmith.Interface.orientation`). -/
structure Orientation (OP : ∀ {p : ℕ} [Fact p.Prime] {k : ℕ}, LocalAction p k → Prop) : Prop where
  /-- The last paragraph of the proof of Proposition 5.1 (05:68-72): on a connected `W`, some open
  subgroup acts preserving orientation. OpenAI takes `G = 2H`, since every homeomorphism of the
  connected `O` preserves or reverses the orientation, so every square preserves it; that needs
  degree theory, and `LocalAction.exists_orientationPreserving_restrict` gets the subgroup from
  continuity of the action at `0` instead (decision 2 of the lead's B-M4 brief). -/
  exists_restrict : ∀ {p : ℕ} [Fact p.Prime] {k : ℕ} (A : LocalAction p k), IsConnected A.W →
    ∃ j, OP (A.restrict j)
  /-- Orientation preservation persists when `G` is replaced by an open subgroup (Lemma 5.3:
  "Faithfulness and orientation preservation persist under this replacement", 05:181-182). -/
  restrict : ∀ {p : ℕ} [Fact p.Prime] {k : ℕ} (A : LocalAction p k) (j : ℕ), OP A →
    OP (A.restrict j)
  /-- With the product orientation on `W = O × ℝ^{d−n}` and the trivial action on the second
  factor, the action still preserves orientation (05:75-80). -/
  stabilize : ∀ {p : ℕ} [Fact p.Prime] {k : ℕ} (A : LocalAction p k) (d : ℕ) (hd : k ≤ d), OP A →
    OP (A.stabilize d hd)

/-- **Lemma 5.2** (collapse and compactification; statement 05:88-103, proof 05:105-133), the
parts beyond Deicyde's multiplicative results: the action extended to `W⁺` is jointly continuous,
and the orbit space `Y = W⁺/ℤ_[p]` is metrizable. (The collapse `c` is continuous by Deicyde's
`HilbertSmith.continuous_collapse`, and `W⁺` is compact metrizable by
`HilbertSmith.metrizableSpace_onePoint`.) Deicyde proves both parts for multiplicative actions
(`HilbertSmith.continuousSMul_onePoint`, `HilbertSmith.metrizableSpace_orbitQuotient`); the
additive bridge is `HilbertSmith.Interface.collapseInput`, which proves this statement. -/
def CollapseInput : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] {k : ℕ} (A : LocalAction p k),
    ContinuousVAdd ℤ_[p] (OnePoint A.W) ∧ TopologicalSpace.MetrizableSpace A.Y

/-- **Lemma 5.3** (an averaged degree-one test; statement 05:135-150, proof 05:152-183), in
OpenAI's pinch form (05:148-149): for a local action on a nonempty `W`, after replacing `ℤ_[p]` by
an open subgroup `p^j ℤ_[p]`, there is `a : Y → S^d` such that `a ∘ q` is homotopic on `W⁺` to a
pinch `P_{z,r}` (`LocalAction.pinch`) supported in a closed ball `B̄(z, r) ⊆ W` of `A.E`'s norm
(OpenAI's round ball; for the stabilized `W = O × ℝ^{d−n}` it is a product of round balls, and the
proof uses no roundness).

Departure (decision 1 of the lead's B-M4 brief): OpenAI states `deg(aqc) = 1` (5.1) in the same
lemma; here it is the theorem `HilbertSmith.Interface.aqc_homotopic_id`, since `P_{z,r} c ≃ id`
(`LocalAction.pinch_comp_c_homotopic`). The pinch `P` is chosen in `LocalAction.pinch`, as the
proof of the lemma allows (05:153-157). Proved as `HilbertSmith.Interface.averagedTest`. -/
def AveragedTest (d : ℕ) : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (A : LocalAction p d), A.W.Nonempty →
    ∃ (j : ℕ) (a : C((A.restrict j).Y, Sphere d)) (z : A.E) (r : ℝ) (hr : 0 < r)
      (hzr : Metric.closedBall z r ⊆ A.W),
      (a.comp (A.restrict j).q).Homotopic ((A.restrict j).pinch z r hr hzr)

/-- **The pinch transport** (the first paragraph of the proof of Proposition 5.8, 05:492-504): on a
connected `W`, any two pinches with closed balls in `W` are homotopic on `W⁺`, by moving the
centre along a path in `W` and shrinking and enlarging the radius at the ends. Proved as
`HilbertSmith.Interface.pinchTransport`. -/
def PinchTransport (d : ℕ) : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (A : LocalAction p d), IsConnected A.W →
    ∀ (z : A.E) (r : ℝ) (hr : 0 < r) (hzr : Metric.closedBall z r ⊆ A.W)
      (z' : A.E) (r' : ℝ) (hr' : 0 < r') (hzr' : Metric.closedBall z' r' ⊆ A.W),
      (A.pinch z r hr hzr).Homotopic (A.pinch z' r' hr' hzr')

/-- **(5.1) from Lemma 5.3's pinch form**: if `a ∘ q ≃ P_{z,r}` on `W⁺`, then `a ∘ q ∘ c ≃ id`,
since `P_{z,r} c ≃ id` (`LocalAction.pinch_comp_c_homotopic`). OpenAI states `deg(aqc) = 1`. -/
theorem aqc_homotopic_id {p : ℕ} [Fact p.Prime] {d : ℕ} (A : LocalAction p d)
    (a : C(A.Y, Sphere d)) {z : A.E} {r : ℝ} {hr : 0 < r} {hzr : Metric.closedBall z r ⊆ A.W}
    (h : (a.comp A.q).Homotopic (A.pinch z r hr hzr)) :
    (a.comp A.qc).Homotopic (ContinuousMap.id _) :=
  (h.comp (ContinuousMap.Homotopic.refl A.c)).trans (A.pinch_comp_c_homotopic z hr hzr)

/-- **Lemmas 5.4 and 5.5, combined** (Lemma 5.4: statement 05:209-224, proof 05:226-275;
Lemma 5.5: statement 05:287-292, proof 05:294-377; combined as in 05:506-512). Let `X` be a
compact metrizable space with a continuous action of `ℤ_[p]`, `q : X → Y` its orbit map, and
`F ⊆ Y` closed. If `v : F → S^d` becomes
nullhomotopic when pulled back to `q⁻¹(F)`, then `D_s ∘ v` is nullhomotopic for some `s`.

Why OpenAI's text gives it, for odd `d ≥ 3` and the telescope maps `D k`: `q⁻¹(F)` is a closed
invariant compact subset of `X` with orbit space `F` (05:508-511); the pullback of `v^*γ_d` to it
is zero, so `v^*γ_d = 0` by Lemma 5.4 (rational orbit pullback); then Lemma 5.5 (killing a
rationally trivial sphere map) gives `s > 0` with `D_s ∘ v` nullhomotopic, where `D_s` is a
composite of the telescope maps `D 2, D 3, …` (05:372-375). -/
def OrbitNull (d : ℕ) (δD : DegreeMaps d) : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (X Y : Type) [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace.MetrizableSpace X] [AddAction ℤ_[p] X] [ContinuousVAdd ℤ_[p] X]
    [TopologicalSpace Y] (q : C(X, Y)), Topology.IsQuotientMap q →
    (∀ x y, q x = q y ↔ ∃ g : ℤ_[p], g +ᵥ x = y) →
    ∀ (F : Set Y), IsClosed F → ∀ v : C(F, Sphere d),
      (v.comp ⟨fun x : q ⁻¹' F => ⟨q x, x.2⟩, by fun_prop⟩).Nullhomotopic →
      ∃ s, ((δD.comp s).comp v).Nullhomotopic

/-- **Lemma 5.6** (finite quotient sheets; statement 05:386-407, proof 05:409-434): for a faithful
action and every `j ≥ 1` there is a sheet region `V` with its multiplier `β` of (5.4). Proved as
`HilbertSmith.Interface.sheetsInput`. -/
def SheetsInput : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] {k : ℕ} (A : LocalAction p k), A.Faithful →
    ∀ j, 1 ≤ j → ∃ V, SheetMultiplier A j V

/-- `S^d` has a basis of contractible open neighbourhoods at every point. Admissible tests need
such a basis at `b_t = t(y∞)` (06:101-107); for tests into `S^d` the TeX does not state it. Proved
as `HilbertSmith.Interface.sphereBasis`, with small caps. -/
def SphereBasis (d : ℕ) : Prop :=
  ∀ x : Sphere d, HasGoodBasisAt x

/-- `C_d` (06:355-358) has a basis of contractible open neighbourhoods at every point. OpenAI
derives this from `C_d` being a smooth `2d`-manifold with boundary (06:359-366);
`HilbertSmith.Interface.closePairBasis` proves it without charts, by explicit contractions of
cap-by-cap boxes. -/
def ClosePairBasis (d : ℕ) : Prop :=
  ∀ z : ClosePair d, HasGoodBasisAt z

/-- **The §5 input the route still assumes**, for the interface `O`: Lemmas 5.4 and 5.5 combined. -/
structure LocalInputs (O : OAIInterface) : Prop where
  /-- Lemmas 5.4 and 5.5, combined (05:209-377, 05:506-512), for the interface's degree maps. -/
  orbitNull : ∀ j, OrbitNull (2 * j + 3) (O.δD j)

end HilbertSmith.Interface
