import HilbertSmithPaper.Categories.Supports.ExteriorQuotient
import HilbertSmithPaper.Categories.Supports.SupportFiltration
import HilbertSmithPaper.Categories.Supports.SupportWhole

/-!
# The exterior quotient as a cut domain

For `Z ⊆ X`, the functor `j_Z : ℬ_{𝐆,Z}(X) → 𝒜_X/𝒜_Z` from the exterior quotient to the quotient
of the support subcategory `𝒜_X` by `𝒜_Z ⊂ 𝒜_X` (`HSP.suppIn Set.univ Z`) is `⟨M⟩ ↦ ⟨M⟩`,
`[u] ↦ [u]`: `Quotient.lift` of `ι⁻¹ ⋙ q'`, where `ι⁻¹ : 𝒜_𝐆(X) → 𝒜_X` is the corestriction of
the identity (`HSP.supportWholeInvFunctor`). It is well defined since a factorization through
`W ∈ 𝒜_Z` in `𝒜_𝐆(X)` is one in `𝒜_X`. It is a strict duality functor with `j_Z ∘ q = q' ∘ ι⁻¹`
(`HSP.exteriorCutIdent`, a subtype bundling these two properties).
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

private theorem lift_compat (Z : Set X) (x y : AsymCat G X) (f₁ f₂ : x ⟶ y)
    (h : FiltQuot.rel (supp Z) f₁ f₂) :
    (supportWholeInvFunctor ⋙ FiltQuot.functor (suppIn Set.univ Z)).map f₁ =
      (supportWholeInvFunctor ⋙ FiltQuot.functor (suppIn Set.univ Z)).map f₂ := by
  obtain ⟨V, hV, a, b, hab⟩ := h
  simp only [Functor.comp_map]
  rw [FiltQuot.functor_map_eq_iff, ← Functor.map_sub, hab]
  exact ⟨⟨V, supp_univ V⟩, hV, ObjectProperty.homMk a, ObjectProperty.homMk b, rfl⟩

/-- The underlying functor of `j_Z`: `⟨M⟩ ↦ ⟨M⟩`, `[u] ↦ [u]`. -/
abbrev exteriorCutIdentAux (Z : Set X) : Ext G X Z ⥤ FiltQuot (suppIn (G := G) Set.univ Z) :=
  CategoryTheory.Quotient.lift (FiltQuot.rel (supp Z))
    (supportWholeInvFunctor ⋙ FiltQuot.functor (suppIn Set.univ Z)) (lift_compat Z)

instance (Z : Set X) : (exteriorCutIdentAux (G := G) Z).Additive where
  map_add {_ _ f g} := by
    obtain ⟨f, rfl⟩ := FiltQuot.functor_map_surjective (supp Z) f
    obtain ⟨g, rfl⟩ := FiltQuot.functor_map_surjective (supp Z) g
    rw [← Functor.map_add, CategoryTheory.Quotient.lift_map_functor_map,
      CategoryTheory.Quotient.lift_map_functor_map,
      CategoryTheory.Quotient.lift_map_functor_map, Functor.map_add]

instance (Z : Set X) : (exteriorCutIdentAux (G := G) Z).Linear ℚ where
  map_smul {_ _} f c := by
    obtain ⟨f, rfl⟩ := FiltQuot.functor_map_surjective (supp Z) f
    rw [← Functor.map_smul, CategoryTheory.Quotient.lift_map_functor_map,
      CategoryTheory.Quotient.lift_map_functor_map, Functor.map_smul]

/-- **The exterior quotient as a cut domain.** The functor `j_Z : ℬ_{𝐆,Z}(X) → 𝒜_X/𝒜_Z`,
`⟨M⟩ ↦ ⟨M⟩`, `[u] ↦ [u]`, is a strict duality functor with `j_Z ∘ q = q' ∘ ι⁻¹`. -/
def exteriorCutIdent (Z : Set X) :
    {j : DualFunctor (Ext G X Z) (FiltQuot (suppIn (G := G) Set.univ Z)) // j.IsStrict ∧
      FiltQuot.functor (supp Z) ⋙ j.toFunctor =
        supportWholeInvFunctor ⋙ FiltQuot.functor (suppIn Set.univ Z)} :=
  ⟨{ toFunctor := exteriorCutIdentAux Z
     ξ M := Iso.refl _
     ξ_natural {M N} f := by
       obtain ⟨f, rfl⟩ := FiltQuot.functor_map_surjective (supp Z) f
       simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
       rw [FiltQuot.dualHom_map, CategoryTheory.Quotient.lift_map_functor_map,
         CategoryTheory.Quotient.lift_map_functor_map]
       rfl
     ξ_dual M := by
       simp only [Iso.refl_hom, dualHom_id, eqToHom_refl, Category.comp_id]
       rfl },
    fun _ => ⟨rfl, rfl⟩, CategoryTheory.Quotient.lift_spec _ _ (lift_compat Z)⟩

end HSP
