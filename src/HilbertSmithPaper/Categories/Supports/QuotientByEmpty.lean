import HilbertSmithPaper.Categories.Supports.SupportFiltration
import HilbertSmithPaper.LTheory.Base.Categories.QuotientDualityFunctor

/-!
# Quotient by the empty support

Every `∅`-supported object is eventually empty, hence a zero object of `𝒜_𝐆(X)`
(`HSP.isZero_of_supp_empty`). So the ideal of maps of `𝒜_S` factoring through `𝒜_∅` is zero, and
the quotient functor `q = FiltQuot.q : 𝒜_S → 𝒜_S/𝒜_∅` is an isomorphism of duality categories
(`HSP.quotientByEmptyIso`): its inverse `q⁻¹ : ⟨M⟩ ↦ M, [u] ↦ u` (`Quotient.lift` of the identity)
is a strict duality functor, and both composites are identity functors. The isomorphism is a
subtype of pairs of duality functors, as for the support subcategory of the whole space.
-/

open CategoryTheory CategoryTheory.Limits Filter

namespace HSP

open DualCat

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

/-- An `∅`-supported object is eventually empty. -/
private theorem eventually_n_eq_zero_of_supp_empty {P : AsymCat G X} (h : supp (∅ : Set X) P) :
    ∀ᶠ i in atTop, P.as.n i = 0 :=
  (h 1 one_pos).mono fun i hi => by
    by_contra hn
    have := hi ⟨0, Nat.pos_of_ne_zero hn⟩
    rw [Metric.thickening_empty] at this
    exact this

/-- An `∅`-supported object is a zero object. -/
private theorem isZero_of_supp_empty {P : AsymCat G X} (h : supp (∅ : Set X) P) : IsZero P := by
  refine (IsZero.iff_id_eq_zero _).2 ?_
  have h1 : AsymCat.mkHom (𝟙 P.as) = AsymCat.mkHom (0 : P.as ⟶ P.as) := by
    rw [AsymCat.mkHom_eq_iff]
    filter_upwards [eventually_n_eq_zero_of_supp_empty h] with i hi
    exact FreeCat.hom_ext (Matrix.ext fun a _ => (Fin.cast (by exact hi) a.2).elim0)
  have h2 : AsymCat.mkHom (𝟙 P.as) = 𝟙 P := CategoryTheory.Functor.map_id _ _
  have h3 : AsymCat.mkHom (0 : P.as ⟶ P.as) = 0 := CategoryTheory.Functor.map_zero _ _ _
  exact h2.symm.trans (h1.trans h3)

/-- The ideal of `𝒜_S` of maps factoring through `𝒜_∅` is zero. -/
private theorem eq_zero_of_ideal_suppIn_empty {S : Set X}
    {M N : (supp S : ObjectProperty (AsymCat G X)).FullSubcategory} {f : M ⟶ N}
    (hf : FiltQuot.ideal (suppIn S ∅) f) : f = 0 := by
  obtain ⟨V, hV, a, b, rfl⟩ := hf
  refine ObjectProperty.hom_ext _ ?_
  rw [ObjectProperty.FullSubcategory.comp_hom, (isZero_of_supp_empty hV).eq_of_tgt a.hom 0,
    Limits.zero_comp]
  rfl

private theorem lift_compat (S : Set X)
    (x y : (supp S : ObjectProperty (AsymCat G X)).FullSubcategory) (f₁ f₂ : x ⟶ y)
    (h : FiltQuot.rel (suppIn S ∅) f₁ f₂) : (𝟭 _).map f₁ = (𝟭 _).map f₂ :=
  sub_eq_zero.1 (eq_zero_of_ideal_suppIn_empty h)

/-- The inverse `q⁻¹ : 𝒜_S/𝒜_∅ → 𝒜_S`, `⟨M⟩ ↦ M`, `[u] ↦ u`. -/
private abbrev quotientByEmptyInvFunctor (S : Set X) :
    FiltQuot (suppIn (G := G) S ∅) ⥤ (supp S : ObjectProperty (AsymCat G X)).FullSubcategory :=
  CategoryTheory.Quotient.lift (FiltQuot.rel (suppIn S ∅)) (𝟭 _) (lift_compat (G := G) S)

instance (S : Set X) : (quotientByEmptyInvFunctor (G := G) S).Additive where
  map_add {_ _ f g} := by
    obtain ⟨f, rfl⟩ := (FiltQuot.functor (suppIn S ∅)).map_surjective f
    obtain ⟨g, rfl⟩ := (FiltQuot.functor (suppIn S ∅)).map_surjective g
    rw [← Functor.map_add, CategoryTheory.Quotient.lift_map_functor_map,
      CategoryTheory.Quotient.lift_map_functor_map,
      CategoryTheory.Quotient.lift_map_functor_map]
    rfl

instance (S : Set X) : (quotientByEmptyInvFunctor (G := G) S).Linear ℚ where
  map_smul {_ _} f c := by
    obtain ⟨f, rfl⟩ := (FiltQuot.functor (suppIn S ∅)).map_surjective f
    rw [← Functor.map_smul, CategoryTheory.Quotient.lift_map_functor_map,
      CategoryTheory.Quotient.lift_map_functor_map]
    rfl

/-- **Quotient by the empty support.** The quotient functor `q : 𝒜_S → 𝒜_S/𝒜_∅` and its inverse
`q⁻¹ : ⟨M⟩ ↦ M, [u] ↦ u` are strict duality functors with `q⁻¹ ∘ q = id` and `q ∘ q⁻¹ = id`. -/
def quotientByEmptyIso (S : Set X) :
    {e : DualFunctor (supp S : ObjectProperty (AsymCat G X)).FullSubcategory
          (FiltQuot (suppIn (G := G) S ∅)) ×
        DualFunctor (FiltQuot (suppIn (G := G) S ∅))
          (supp S : ObjectProperty (AsymCat G X)).FullSubcategory //
      e.1 = FiltQuot.q (suppIn S ∅) ∧ e.1.IsStrict ∧ e.2.IsStrict ∧
        e.1.toFunctor ⋙ e.2.toFunctor = 𝟭 _ ∧ e.2.toFunctor ⋙ e.1.toFunctor = 𝟭 _} :=
  ⟨(FiltQuot.q (suppIn S ∅),
      { toFunctor := quotientByEmptyInvFunctor S
        ξ M := Iso.refl _
        ξ_natural {M N} f := by
          obtain ⟨f, rfl⟩ := (FiltQuot.functor (suppIn S ∅)).map_surjective f
          simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
          rw [FiltQuot.dualHom_map, CategoryTheory.Quotient.lift_map_functor_map,
            CategoryTheory.Quotient.lift_map_functor_map]
          rfl
        ξ_dual M := by
          simp only [Iso.refl_hom, dualHom_id, eqToHom_refl, Category.comp_id]
          rfl }),
    rfl, FiltQuot.q_isStrict _, fun _ => ⟨rfl, rfl⟩,
    CategoryTheory.Quotient.lift_spec _ _ (lift_compat (G := G) S),
    CategoryTheory.Quotient.lift_unique' _ _ _ (by
      rw [← Functor.assoc]
      change (FiltQuot.functor (suppIn S ∅) ⋙ quotientByEmptyInvFunctor S) ⋙ _ = _
      rw [CategoryTheory.Quotient.lift_spec]
      rfl)⟩

end HSP
