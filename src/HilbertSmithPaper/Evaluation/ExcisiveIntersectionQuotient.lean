import HilbertSmithPaper.Categories.Supports.RelativeIntersectionAdditive
import HilbertSmithPaper.Categories.Supports.SupportFiltration

/-!
# Quotient of an excisive intersection

Let `S, A, B ⊆ X` with `A` compact, `B` closed and `A ∩ B = ∅`. Inside `𝒜_S`, let `𝒰_A`
and `𝒰_B` be the `A`- and `B`-supported objects. An object of `𝒰_A ∩ 𝒰_B` is eventually empty: for
`δ > 0` with disjoint `δ`-thickenings of `A` and `B`, eventually no label lies in both. So the
functor `𝒰_A/(𝒰_A ∩ 𝒰_B) → 𝒜_A/𝒜_∅`, `M ↦ M`, `[u] ↦ [u]`, is a well defined
strict duality functor (`HSP.excisiveInterQuotIso`, a subtype of duality functors). It is an
isomorphism of categories, with inverse `M ↦ M`, `[u] ↦ [u]`; this is not formalized.
-/

open CategoryTheory CategoryTheory.Limits Filter Metric

namespace HSP

open DualCat

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

section

variable {S A B : Set X}

/-- An object supported on two sets with disjoint thickenings is `∅`-supported. -/
private theorem supp_empty_of (hA : IsCompact A) (hB : IsClosed B) (hAB : Disjoint A B)
    {P : AsymCat G X} (hPA : supp A P) (hPB : supp B P) : supp (∅ : Set X) P := by
  obtain ⟨δ, hδ, hd⟩ := hAB.exists_thickenings hA hB
  intro ε _
  filter_upwards [hPA δ hδ, hPB δ hδ] with i hi hi' k
  exact (Set.disjoint_left.1 hd (hi k) (hi' k)).elim

variable (S A) in
/-- `𝒰_A → 𝒜_A`, `M ↦ M`, `u ↦ u`. -/
private abbrev toSupp :
    (suppIn (G := G) S A).FullSubcategory ⥤
      (supp A : ObjectProperty (AsymCat G X)).FullSubcategory :=
  ObjectProperty.lift _ ((suppIn S A).ι ⋙ (supp S).ι) fun M => M.property

private instance : (toSupp (G := G) S A).Additive where
  map_add := ObjectProperty.hom_ext _ rfl

private instance : (toSupp (G := G) S A).Linear ℚ where
  map_smul _ _ := ObjectProperty.hom_ext _ rfl

private theorem toSupp_compat (hA : IsCompact A) (hB : IsClosed B) (hAB : Disjoint A B)
    (x y : (suppIn (G := G) S A).FullSubcategory) (f₁ f₂ : x ⟶ y)
    (h : FiltQuot.rel (ExcisivePair.inter (suppIn S A) (suppIn S B)) f₁ f₂) :
    (toSupp S A ⋙ FiltQuot.functor (suppIn A ∅)).map f₁ =
      (toSupp S A ⋙ FiltQuot.functor (suppIn A ∅)).map f₂ := by
  obtain ⟨W, hW, a, b, hab⟩ := h
  rw [Functor.comp_map, Functor.comp_map, FiltQuot.functor_map_eq_iff]
  refine ⟨(toSupp S A).obj W, supp_empty_of hA hB hAB W.property hW, (toSupp S A).map a,
    (toSupp S A).map b, ?_⟩
  rw [← Functor.map_sub, ← Functor.map_comp, hab]

variable (B) in
/-- `𝒰_A/(𝒰_A ∩ 𝒰_B) → 𝒜_A/𝒜_∅`, `[u] ↦ [u]`. -/
private abbrev fwdFunctor (hA : IsCompact A) (hB : IsClosed B) (hAB : Disjoint A B) :
    FiltQuot (ExcisivePair.inter (suppIn (G := G) S A) (suppIn S B)) ⥤
      FiltQuot (suppIn (G := G) A ∅) :=
  CategoryTheory.Quotient.lift _ (toSupp S A ⋙ FiltQuot.functor (suppIn A ∅))
    (toSupp_compat hA hB hAB)

private instance (hA : IsCompact A) (hB : IsClosed B) (hAB : Disjoint A B) :
    (fwdFunctor (G := G) (S := S) B hA hB hAB).Additive where
  map_add {_ _ f g} := by
    obtain ⟨f, rfl⟩ := (FiltQuot.functor _).map_surjective f
    obtain ⟨g, rfl⟩ := (FiltQuot.functor _).map_surjective g
    rw [← Functor.map_add, CategoryTheory.Quotient.lift_map_functor_map,
      CategoryTheory.Quotient.lift_map_functor_map,
      CategoryTheory.Quotient.lift_map_functor_map, Functor.map_add]

private instance (hA : IsCompact A) (hB : IsClosed B) (hAB : Disjoint A B) :
    (fwdFunctor (G := G) (S := S) B hA hB hAB).Linear ℚ where
  map_smul {_ _} f c := by
    obtain ⟨f, rfl⟩ := (FiltQuot.functor _).map_surjective f
    rw [← Functor.map_smul, CategoryTheory.Quotient.lift_map_functor_map,
      CategoryTheory.Quotient.lift_map_functor_map, Functor.map_smul]

variable (B) in
/-- The forward functor as a strict duality functor. -/
private def fwdDual (hA : IsCompact A) (hB : IsClosed B) (hAB : Disjoint A B) :
    DualFunctor (FiltQuot (ExcisivePair.inter (suppIn (G := G) S A) (suppIn S B)))
      (FiltQuot (suppIn (G := G) A ∅)) where
  toFunctor := fwdFunctor B hA hB hAB
  ξ _ := Iso.refl _
  ξ_natural {M N} f := by
    obtain ⟨f, rfl⟩ := (FiltQuot.functor _).map_surjective f
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rw [FiltQuot.dualHom_map, CategoryTheory.Quotient.lift_map_functor_map,
      CategoryTheory.Quotient.lift_map_functor_map, Functor.comp_map, Functor.comp_map,
      FiltQuot.dualHom_map]
    exact congrArg (FiltQuot.functor _).map (ObjectProperty.hom_ext _ rfl)
  ξ_dual M := by
    simp only [Iso.refl_hom, dualHom_id, eqToHom_refl, Category.comp_id]
    rfl


end

/-- **Quotient of an excisive intersection.** For `A` compact, `B` closed and
`A ∩ B = ∅`, the functor `e : 𝒰_A/(𝒰_A ∩ 𝒰_B) → 𝒜_A/𝒜_∅` induced by `M ↦ M`, `u ↦ u`
(characterized by `q ⋙ e = ι ⋙ q`) is a strict duality functor. -/
noncomputable def excisiveInterQuotIso (S : Set X) {A B : Set X} (hA : IsCompact A)
    (hB : IsClosed B) (hAB : Disjoint A B) :
    {e : DualFunctor (FiltQuot (ExcisivePair.inter (suppIn (G := G) S A) (suppIn S B)))
          (FiltQuot (suppIn (G := G) A ∅)) //
      FiltQuot.functor _ ⋙ e.toFunctor =
          ObjectProperty.lift _ ((suppIn S A).ι ⋙ (supp S).ι) (fun M => M.property) ⋙
            FiltQuot.functor (suppIn A ∅) ∧ e.IsStrict} :=
  ⟨fwdDual B hA hB hAB, CategoryTheory.Quotient.lift_spec _ _ (toSupp_compat hA hB hAB),
    fun _ => ⟨rfl, rfl⟩⟩

end HSP
