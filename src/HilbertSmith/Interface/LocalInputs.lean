import HilbertSmith.Interface.Invariant

/-!
# The topology of §5 that the route assumes

OpenAI's §5 prepares the local test that §6 consumes. B1 bundled it into one field
`LocalTests.source`; following PLAN §3.2 (change 3) it is split here into its pieces, each a `Prop`
stated as close to OpenAI's text as the formal layer allows, so that each can later be proved or
kept as a published input on its own.

* `ChartReduction`: what §6 uses of Proposition 5.1, without its orientation step.
* `Orientation OP`: the facts about the orientation predicate `OP` that §5 uses: the step
  `G = 2H` of Proposition 5.1, and persistence under the replacements of §5.
* `CollapseInput`: Lemma 5.2 (the extended action is continuous; the orbit space is metrizable).
* `AveragedTest d`: Lemma 5.3, together with the pinch transport of the first paragraph of the
  proof of Proposition 5.8.
* `OrbitNull d δD`: Lemmas 5.4 and 5.5 combined, in the form the proof of Proposition 5.8 uses.
* `SheetsInput`: Lemma 5.6.
* `SphereBasis d`, `ClosePairBasis d`: good neighbourhood bases on `S^d` and `C_d` (06:357-366).
* `LocalInputs O`: all of them, for the interface `O`.

Lemma 5.7 is not an input: it is Deicyde's `HilbertSmith.homotopyExtension`.

Two departures from PLAN §3.2, accepted in the lead's review of 2026-11-07 (PLAN §3.4 amended):
* Lemmas 5.4 and 5.5 are stated about rational Čech cohomology, which neither Mathlib nor TauCeti
  has. `OrbitNull` is their composite, which needs no cohomology: if `v ∘ r` is nullhomotopic for
  an orbit map `r`, then `v^*γ_d` vanishes after pulling back, hence vanishes (Lemma 5.4), hence
  some `D_s ∘ v` is nullhomotopic (Lemma 5.5). It splits into the two lemmas once a Čech
  cohomology of compact metrizable spaces is available.
* The pinch transport is part of `AveragedTest`: stating it alone needs OpenAI's pinch maps
  `P_{z,r}` as definitions. It is split off at B-M4, once they are defined.

Scope and non-vacuity. Each input is stated for the actions OpenAI's text covers, or more: Prop 5.1
for faithful actions on second-countable manifolds; Lemma 5.2 for any action; Lemma 5.3 for any
action on a connected `W`; `OrbitNull` for odd `d ≥ 3`, true when the maps `D k` of the interface
really have degree `k`; Lemma 5.6 for faithful actions. `LocalAction`s of every kind are
quantified over, but each input assumes what its lemma needs, so each holds by the cited result.
-/

namespace HilbertSmith.Interface

open Topology Set

universe u

/-- **Proposition 5.1, without the orientation step** (an invariant chart subset; 05:14-21,
proof 05:23-73), in the form §6 uses it: a faithful jointly continuous action of `ℤ_[p]` on a
connected Hausdorff second-countable `n`-manifold gives a faithful action of `ℤ_[p]` on a connected
open subset of an `n`-dimensional real normed space.

OpenAI's Proposition 5.1 says more: an open subgroup `G ≅ ℤ_[p]` acts faithfully on a connected
`G`-invariant open subset `O` of a chart of `M`, which is then regarded as an open subset of `ℝⁿ`
(05:16-20). The formal statement drops the subgroup and the chart, because `Main` uses neither:
it uses only the action on `O ⊆ ℝⁿ`, re-identifying `G` with `ℤ_[p]`. The orientation step
(05:68-72) is `Orientation.exists_restrict`.

OpenAI states it under the standing hypotheses of §5, which include second countability (05:4-6);
its proof never uses it (PLAN §0), which B-M3 is to show by proving this statement without
`[SecondCountableTopology M]` from `HilbertSmith.NewmanInput`. In a build that imports HS_proof,
this statement follows ex falso from HS_proof's p-adic exclusion (`HSBridge.hs_route_univ`), so
B-M3's proof must pass the route-separation audit with only `HSBridge.newmanInput` allowed. -/
def ChartReduction : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [ConnectedSpace M]
    [AddAction ℤ_[p] M] [ContinuousVAdd ℤ_[p] M], FaithfulVAdd ℤ_[p] M →
    ∃ A : LocalAction p n, IsConnected A.W ∧ A.Faithful

/-- **What §5 uses about orientation preservation**, for the predicate `OP` of the interface. -/
structure Orientation (OP : ∀ {p : ℕ} [Fact p.Prime] {k : ℕ}, LocalAction p k → Prop) : Prop where
  /-- The last paragraph of the proof of Proposition 5.1 (05:66-72): every homeomorphism of the
  connected `O` preserves or reverses the orientation from the chart, so every square preserves
  it, and `G = 2H` (that is `H` for odd `p`, and `pH` for `p = 2`) acts preserving orientation. -/
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
parts not already proved: the action extended to `W⁺` is jointly continuous, and the orbit space
`Y = W⁺/ℤ_[p]` is metrizable. (The
collapse `c` is continuous by Deicyde's `HilbertSmith.continuous_collapse`, and `W⁺` is compact
metrizable by `HilbertSmith.metrizableSpace_onePoint`.) Deicyde proves both parts for
multiplicative actions (`HilbertSmith.continuousSMul_onePoint`,
`HilbertSmith.metrizableSpace_orbitQuotient`); passing to the additive `ℤ_[p]` is B-M3 work. -/
def CollapseInput : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] {k : ℕ} (A : LocalAction p k),
    ContinuousVAdd ℤ_[p] (OnePoint A.W) ∧ TopologicalSpace.MetrizableSpace A.Y

/-- **Lemma 5.3** (an averaged degree-one test; statement 05:135-150, proof 05:152-183), with the
pinch transport from the proof of Proposition 5.8. After replacing `ℤ_[p]` by an open subgroup
`p^j ℤ_[p]`, there is `a : Y → S^d` with:
* `a ∘ q ∘ c ≃ id`. OpenAI states `deg(aqc) = 1` (5.1) and, in the same statement, that `aq` is
  homotopic on `W⁺` to a degree-one pinch `P_{z,r}` supported in a round ball in `W`
  (05:148-149). Choosing `P` through `A.sphereEquiv` and a radial homeomorphism of the open unit
  ball onto `ℝ^d`, `P_{z,r} ∘ c ≃ id` holds by an explicit scaling homotopy, with no degree theory.
  So `aqc ≃ id` follows from the lemma's second assertion; stating it avoids degree theory, as B1
  proposed.
* for every nonempty open `V ⊆ Y ∖ {y∞}`, `a ∘ q` is homotopic on `W⁺` to a map constant on
  `q⁻¹(Y ∖ V)`: the first paragraph of the proof of Proposition 5.8 (05:492-506) moves the pinch
  along a path in the connected `W` into a ball inside `q⁻¹(V)`.

This needs `W` connected; it is applied to `W = O × ℝ^{d−n}`. -/
def AveragedTest (d : ℕ) : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (A : LocalAction p d), IsConnected A.W →
    ∃ (j : ℕ) (a : C((A.restrict j).Y, Sphere d)),
      (a.comp (A.restrict j).qc).Homotopic (ContinuousMap.id _) ∧
      ∀ V : Set (A.restrict j).Y, IsOpen V → V.Nonempty → (A.restrict j).yinf ∉ V →
        ∃ φ : C(OnePoint (A.restrict j).W, Sphere d), (a.comp (A.restrict j).q).Homotopic φ ∧
          ∃ b, ∀ x, (A.restrict j).q x ∉ V → φ x = b

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
action and every `j ≥ 1` there is a sheet region `V` with its multiplier `β` of (5.2). -/
def SheetsInput : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] {k : ℕ} (A : LocalAction p k), A.Faithful →
    ∀ j, 1 ≤ j → ∃ V, SheetMultiplier A j V

/-- `S^d` has a basis of contractible open neighbourhoods at every point (06:357-366, applied to
`b_t = t(y∞)` for tests `t` into `S^d`). -/
def SphereBasis (d : ℕ) : Prop :=
  ∀ x : Sphere d, HasGoodBasisAt x

/-- `C_d` has a basis of contractible open neighbourhoods at every point: it is a smooth
`2d`-manifold with boundary (06:359-366). -/
def ClosePairBasis (d : ℕ) : Prop :=
  ∀ z : ClosePair d, HasGoodBasisAt z

/-- **The §5 inputs of the route**, for the interface `O`. -/
structure LocalInputs (O : OAIInterface) : Prop where
  /-- Proposition 5.1 without its orientation step (05:14-73), with second countability. -/
  chartReduction : ChartReduction.{u}
  /-- The orientation facts of §5, for the interface's `OP` (05:68-72, 05:75-80, 05:181-182). -/
  orientation : Orientation O.OP
  /-- Lemma 5.2 (05:88-133). -/
  collapse : CollapseInput
  /-- Lemma 5.3 with the pinch transport (05:135-183, 05:491-506), in every odd dimension
  `2j + 3`. -/
  averagedTest : ∀ j, AveragedTest (2 * j + 3)
  /-- Lemmas 5.4 and 5.5, combined (05:209-377, 05:506-512), for the interface's degree maps. -/
  orbitNull : ∀ j, OrbitNull (2 * j + 3) (O.δD j)
  /-- Lemma 5.6 (05:386-434). -/
  sheets : SheetsInput
  /-- Good neighbourhood bases on spheres (06:357-366). -/
  sphereBasis : ∀ d, SphereBasis d
  /-- Good neighbourhood bases on close-pair tests (06:359-366). -/
  closePairBasis : ∀ d, ClosePairBasis d

end HilbertSmith.Interface
