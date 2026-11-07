import HilbertSmith.Interface.LocalInputs

/-!
# Moving a test into a prescribed open set

Proposition 5.8 of OpenAI's preprint, from the pinch transport (part of `AveragedTest`) and
Lemmas 5.4 and 5.5 (`OrbitNull`), which are fields of `HilbertSmith.Interface.LocalInputs`, Lemma
5.2 (`CollapseInput`, proved as `HilbertSmith.Interface.collapseInput`) and Lemma 5.7 (Deicyde's
`HilbertSmith.homotopyExtension`).
-/

namespace HilbertSmith.Interface

open Topology Set

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

end HilbertSmith.Interface
