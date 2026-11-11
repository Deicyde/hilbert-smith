import HilbertSmithPaper.Categories.Supports.SupportSubcategory
import HilbertSmithPaper.LTheory.Base.Categories.DualSubcategory

/-!
# The support subcategory of the whole space

Every object of `𝒜_𝐆(X)` lies in `𝒜_X` (`HSP.supp_univ`), and the inclusion
`ι = DualSubcategory.incl : 𝒜_X → 𝒜_𝐆(X)` is an isomorphism of duality categories
(`HSP.supportWholeIso`): together with its inverse `ι⁻¹ : M ↦ M, u ↦ u` (the corestriction of the
identity functor, `ObjectProperty.lift`), both strict duality functors, with `ι⁻¹ ∘ ι = id` and
`ι ∘ ι⁻¹ = id` as equalities of functors. As for the iterated bounded quotients, the isomorphism
is a subtype of pairs of duality functors.
-/

open CategoryTheory CategoryTheory.Limits Filter

namespace HSP

open DualCat

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

/-- Every object of `𝒜_𝐆(X)` is `X`-supported. -/
private theorem supp_univ (P : AsymCat G X) : supp (Set.univ : Set X) P := fun _ hε =>
  Eventually.of_forall fun _ _ => Metric.self_subset_thickening hε _ (Set.mem_univ _)

/-- The corestriction `ι⁻¹ : 𝒜_𝐆(X) → 𝒜_X` of the identity functor, `M ↦ M`, `u ↦ u`. -/
private abbrev supportWholeInvFunctor :
    AsymCat G X ⥤ (supp (Set.univ : Set X) : ObjectProperty (AsymCat G X)).FullSubcategory :=
  ObjectProperty.lift _ (𝟭 _) supp_univ

instance : (supportWholeInvFunctor (G := G) (X := X)).Additive where
  map_add := rfl

instance : (supportWholeInvFunctor (G := G) (X := X)).Linear ℚ where
  map_smul _ _ := rfl

/-- **The support subcategory of the whole space.** The inclusion `ι : 𝒜_X → 𝒜_𝐆(X)` and the
corestriction `ι⁻¹ : 𝒜_𝐆(X) → 𝒜_X` of the identity functor are strict duality functors with
`ι⁻¹ ∘ ι = id` and `ι ∘ ι⁻¹ = id`. -/
def supportWholeIso :
    {e : DualFunctor (supp (Set.univ : Set X) : ObjectProperty (AsymCat G X)).FullSubcategory
          (AsymCat G X) ×
        DualFunctor (AsymCat G X)
          (supp (Set.univ : Set X) : ObjectProperty (AsymCat G X)).FullSubcategory //
      e.1 = DualSubcategory.incl (supp Set.univ) ∧ e.1.IsStrict ∧ e.2.IsStrict ∧
        e.1.toFunctor ⋙ e.2.toFunctor = 𝟭 _ ∧ e.2.toFunctor ⋙ e.1.toFunctor = 𝟭 _} :=
  ⟨(DualSubcategory.incl (supp Set.univ),
      { toFunctor := supportWholeInvFunctor
        ξ M := Iso.refl _
        ξ_natural f := by simp; rfl
        ξ_dual M := by simp; rfl }),
    rfl, DualSubcategory.incl_isStrict _, fun _ => ⟨rfl, rfl⟩, rfl, rfl⟩

end HSP
