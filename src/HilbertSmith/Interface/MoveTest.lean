import HilbertSmith.Interface.LocalInputs

/-!
# Moving a test into a prescribed open set

Proposition 5.8 of OpenAI's preprint, from the pinch transport (`PinchTransport`, used through
`hpinch_of` with Lemma 5.3's pinch form) and Lemmas 5.4 and 5.5 (`OrbitNull`), which are fields of
`HilbertSmith.Interface.LocalInputs`, Lemma 5.2 (`CollapseInput`, proved as
`HilbertSmith.Interface.collapseInput`) and Lemma 5.7 (Deicyde's `HilbertSmith.homotopyExtension`).
-/

namespace HilbertSmith.Interface

open Topology Set OnePoint

/-- **Proposition 5.8** (moving a test into a prescribed open set). Let `a : Y → S^d` be such
that, for every nonempty open `V ⊆ Y ∖ {y∞}`, `a ∘ q` is homotopic on `W⁺` to a map constant on
`q⁻¹(Y ∖ V)` (the pinch transport). Then for every such `V` there are `s` and `h : Y → S^d` with
`h ≃ D_s ∘ a` and `h` constant on `Y ∖ V`.

Proof (05:491-517): `a ∘ q` restricted to `q⁻¹(F)`, `F = Y ∖ V`, is nullhomotopic; by `OrbitNull`
(Lemmas 5.4 and 5.5), `D_s ∘ a|_F` is nullhomotopic for some `s`; extending that nullhomotopy from
the closed set `F` to `Y` (Lemma 5.7, `HilbertSmith.homotopyExtension`; `Y` is compact metrizable
by Lemma 5.2) and taking its endpoint gives `h`. -/
theorem moveTest {d : ℕ} {δD : DegreeMaps d} (hN : OrbitNull d δD) (hC : CollapseInput)
    {p : ℕ} [Fact p.Prime] (A : LocalAction p d) (a : C(A.Y, Sphere d))
    (hpinch : ∀ V : Set A.Y, IsOpen V → V.Nonempty → A.yinf ∉ V →
      ∃ φ : C(OnePoint A.W, Sphere d), (a.comp A.q).Homotopic φ ∧
        ∃ b, ∀ x, A.q x ∉ V → φ x = b)
    (V : Set A.Y) (hV : IsOpen V) (hVne : V.Nonempty) (hinf : A.yinf ∉ V) :
    ∃ (s : ℕ) (h : C(A.Y, Sphere d)), h.Homotopic ((δD.comp s).comp a) ∧
      ∀ y ∉ V, h y = h A.yinf := by
  -- The closed set `F = Y ∖ V`, which contains `y∞`.
  set F : Set A.Y := Vᶜ
  have hF : IsClosed F := hV.isClosed_compl
  have hinfF : A.yinf ∈ F := hinf
  obtain ⟨φ, hφ, b, hb⟩ := hpinch V hV hVne hinf
  -- `a|_F`, pulled back to `q⁻¹(F)`, is nullhomotopic: restrict the pinch homotopy.
  let v : C(F, Sphere d) := a.comp ⟨Subtype.val, continuous_subtype_val⟩
  let j : C(A.q ⁻¹' F, OnePoint A.W) := ⟨Subtype.val, continuous_subtype_val⟩
  have hnull : (v.comp ⟨fun x : A.q ⁻¹' F => ⟨A.q x, x.2⟩, by fun_prop⟩).Nullhomotopic := by
    refine ⟨b, ?_⟩
    have h1 : ((a.comp A.q).comp j).Homotopic (φ.comp j) :=
      hφ.comp (ContinuousMap.Homotopic.refl j)
    have h2 : φ.comp j = ContinuousMap.const _ b := ContinuousMap.ext fun x => hb x.1 x.2
    rw [← h2]
    exact h1
  -- Apply `OrbitNull` to the orbit map `q : W⁺ → Y`.
  have : TopologicalSpace.MetrizableSpace (OnePoint A.W) := metrizableSpace_onePoint A.W A.isOpen
  have : ContinuousVAdd ℤ_[p] (OnePoint A.W) := (hC A).1
  have : TopologicalSpace.MetrizableSpace A.Y := (hC A).2
  have hq : IsQuotientMap A.q := isQuotientMap_quotient_mk'
  have horb : ∀ x y, A.q x = A.q y ↔ ∃ g : ℤ_[p], g +ᵥ x = y := by
    intro x y
    change Quotient.mk _ x = Quotient.mk _ y ↔ _
    rw [Quotient.eq, AddAction.orbitRel_apply, AddAction.mem_orbit_iff]
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨-g, by rw [← hg, neg_vadd_vadd]⟩
    · rintro ⟨g, hg⟩
      exact ⟨-g, by rw [← hg, neg_vadd_vadd]⟩
  obtain ⟨s, y₀, ⟨G⟩⟩ := hN (OnePoint A.W) A.Y A.q hq horb F hF v hnull
  -- Extend the nullhomotopy of `D_s ∘ a|_F` from `F` to `Y` (Lemma 5.7).
  let f : C(A.Y, Sphere d) := (δD.comp s).comp a
  let H : C(↥F × Interval, Sphere d) := ⟨fun z => G (z.2, z.1), by fun_prop⟩
  have hH0 : ∀ z : ↥F, H (z, time0) = f z := fun z => G.apply_zero z
  obtain ⟨Ht, hHt0, hHtF⟩ := homotopyExtension hF f H hH0
  let h : C(A.Y, Sphere d) := ⟨fun y => Ht (y, 1), by fun_prop⟩
  have hy₀ : ∀ y ∈ F, h y = y₀ := fun y hy => (hHtF (⟨y, hy⟩, 1)).trans (G.apply_one _)
  refine ⟨s, h, ContinuousMap.Homotopic.symm ⟨?_⟩, fun y hy => (hy₀ y hy).trans (hy₀ _ hinfF).symm⟩
  exact
    { toFun := fun z => Ht (z.2, z.1)
      continuous_toFun := by fun_prop
      map_zero_left := fun y => hHt0 y
      map_one_left := fun _ => rfl }

/-- **The hypothesis of `moveTest` from Lemma 5.3's pinch form and the pinch transport** (the first
paragraph of the proof of Proposition 5.8, 05:492-506). If `a ∘ q ≃ P_{z,r}` and `P_{z,r}` is
homotopic to every pinch with closed ball in `W`, then for every nonempty open `V ⊆ Y ∖ {y∞}`,
`a ∘ q` is homotopic to a pinch whose ball lies in the open set `q⁻¹(V)`, which misses `∞` because
`y∞ ∉ V`; that pinch is constant `ξ` on `q⁻¹(Y ∖ V)`. -/
theorem hpinch_of {p : ℕ} [Fact p.Prime] {d : ℕ} (A : LocalAction p d) (a : C(A.Y, Sphere d))
    {z : A.E} {r : ℝ} {hr : 0 < r} {hzr : Metric.closedBall z r ⊆ A.W}
    (ha : (a.comp A.q).Homotopic (A.pinch z r hr hzr))
    (ht : ∀ (z' : A.E) (r' : ℝ) (hr' : 0 < r') (hzr' : Metric.closedBall z' r' ⊆ A.W),
      (A.pinch z r hr hzr).Homotopic (A.pinch z' r' hr' hzr'))
    (V : Set A.Y) (hV : IsOpen V) (hVne : V.Nonempty) (hinf : A.yinf ∉ V) :
    ∃ φ : C(OnePoint A.W, Sphere d), (a.comp A.q).Homotopic φ ∧
      ∃ b, ∀ x, A.q x ∉ V → φ x = b := by
  -- The open set `U ⊆ E` of points of `W` whose image lies in `V`.
  set U : Set A.E := Subtype.val '' (((↑) : A.W → OnePoint A.W) ⁻¹' (A.q ⁻¹' V))
  have hU : IsOpen U := A.isOpen.isOpenMap_subtype_val _
    ((hV.preimage A.q.continuous).preimage OnePoint.continuous_coe)
  obtain ⟨y, hy⟩ := hVne
  obtain ⟨x, rfl⟩ : ∃ x, A.q x = y := Quotient.exists_rep y
  induction x using OnePoint.rec with
  | infty => exact absurd hy hinf
  | coe w =>
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU w ⟨w, hy, rfl⟩
    have hsub : Metric.closedBall (w : A.E) (ε / 2) ⊆ U :=
      (Metric.closedBall_subset_ball (by linarith)).trans hball
    have hsubW : Metric.closedBall (w : A.E) (ε / 2) ⊆ A.W := fun v hv => by
      obtain ⟨w', -, rfl⟩ := hsub hv
      exact w'.2
    refine ⟨A.pinch w (ε / 2) (by linarith) hsubW, ha.trans (ht _ _ _ _), A.sphereEquiv ∞,
      fun x hx => ?_⟩
    induction x using OnePoint.rec with
    | infty => rfl
    | coe w' =>
      refine A.pinch_apply_of_notMem _ _ fun hw' => hx ?_
      obtain ⟨w'', hw'', hww⟩ := hsub hw'
      rwa [← Subtype.ext hww]

end HilbertSmith.Interface
