import HilbertSmithPaper.Categories.Supports.ExteriorQuotient

/-!
# Induced functor on exterior quotients

Let `F : 𝒜_𝐆(X) → 𝒜_𝐆'(X')` be a strict duality functor with `F(𝒜_Z) ⊆ 𝒜_{Z'}` (on objects). The
induced functor `F̄ : ℬ_{𝐆,Z}(X) → ℬ_{𝐆',Z'}(X')`, `⟨M⟩ ↦ ⟨F M⟩`, `[u] ↦ [F u]`, is
`Quotient.lift` of `F ⋙ q'` (well defined because `F` carries a factorization through
`W ∈ 𝒜_Z` to one through `F W ∈ 𝒜_{Z'}`), with `ξ̄_M = q'(ξ_M)`. It is a strict duality functor
with `F̄ ∘ q = q' ∘ F` (`HSP.extFunctor`, a subtype bundling these two properties).
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

variable {p : ℕ} {G G' : GroupSeq p} {X X' : Type*} [MetricSpace X] [AddAction (ZMod p) X]
  [MetricSpace X'] [AddAction (ZMod p) X']

private theorem lift_compat (F : DualFunctor (AsymCat G X) (AsymCat G' X')) {Z : Set X}
    {Z' : Set X'} (hZ : ∀ P, supp Z P → supp Z' (F.toFunctor.obj P)) (x y : AsymCat G X)
    (f₁ f₂ : x ⟶ y) (h : FiltQuot.rel (supp Z) f₁ f₂) :
    (F.toFunctor ⋙ FiltQuot.functor (supp Z')).map f₁ =
      (F.toFunctor ⋙ FiltQuot.functor (supp Z')).map f₂ := by
  obtain ⟨V, hV, a, b, hab⟩ := h
  simp only [Functor.comp_map]
  rw [FiltQuot.functor_map_eq_iff, ← F.toFunctor.map_sub, hab, F.toFunctor.map_comp]
  exact ⟨_, hZ V hV, _, _, rfl⟩

/-- The underlying functor of `F̄`: `⟨M⟩ ↦ ⟨F M⟩`, `[u] ↦ [F u]`. -/
private abbrev extFunctorAux (F : DualFunctor (AsymCat G X) (AsymCat G' X')) {Z : Set X} {Z' : Set X'}
    (hZ : ∀ P, supp Z P → supp Z' (F.toFunctor.obj P)) : Ext G X Z ⥤ Ext G' X' Z' :=
  CategoryTheory.Quotient.lift (FiltQuot.rel (supp Z)) (F.toFunctor ⋙ FiltQuot.functor (supp Z'))
    (lift_compat F hZ)

private instance (F : DualFunctor (AsymCat G X) (AsymCat G' X')) {Z : Set X} {Z' : Set X'}
    (hZ : ∀ P, supp Z P → supp Z' (F.toFunctor.obj P)) : (extFunctorAux F hZ).Additive where
  map_add {_ _ f g} := by
    obtain ⟨f, rfl⟩ := (FiltQuot.functor (supp Z)).map_surjective f
    obtain ⟨g, rfl⟩ := (FiltQuot.functor (supp Z)).map_surjective g
    rw [← Functor.map_add, CategoryTheory.Quotient.lift_map_functor_map,
      CategoryTheory.Quotient.lift_map_functor_map,
      CategoryTheory.Quotient.lift_map_functor_map, Functor.map_add]

private instance (F : DualFunctor (AsymCat G X) (AsymCat G' X')) {Z : Set X} {Z' : Set X'}
    (hZ : ∀ P, supp Z P → supp Z' (F.toFunctor.obj P)) : (extFunctorAux F hZ).Linear ℚ where
  map_smul {_ _} f c := by
    obtain ⟨f, rfl⟩ := (FiltQuot.functor (supp Z)).map_surjective f
    rw [← Functor.map_smul, CategoryTheory.Quotient.lift_map_functor_map,
      CategoryTheory.Quotient.lift_map_functor_map, Functor.map_smul]

/-- **Induced functor on exterior quotients.** For a strict duality functor
`F : 𝒜_𝐆(X) → 𝒜_𝐆'(X')` with `F(𝒜_Z) ⊆ 𝒜_{Z'}`, the induced functor
`F̄ : ℬ_{𝐆,Z}(X) → ℬ_{𝐆',Z'}(X')`, `⟨M⟩ ↦ ⟨F M⟩`, `[u] ↦ [F u]`, is a strict duality functor with
`F̄ ∘ q = q' ∘ F`. -/
def extFunctor (F : DualFunctor (AsymCat G X) (AsymCat G' X')) (hF : F.IsStrict) {Z : Set X}
    {Z' : Set X'} (hZ : ∀ P, supp Z P → supp Z' (F.toFunctor.obj P)) :
    {Fb : DualFunctor (Ext G X Z) (Ext G' X' Z') // Fb.IsStrict ∧
      FiltQuot.functor (supp Z) ⋙ Fb.toFunctor = F.toFunctor ⋙ FiltQuot.functor (supp Z')} :=
  ⟨{ toFunctor := extFunctorAux F hZ
     ξ M := (FiltQuot.functor (supp Z')).mapIso (F.ξ M.as)
     ξ_natural {M N} f := by
       obtain ⟨f, rfl⟩ := (FiltQuot.functor (supp Z)).map_surjective f
       simp only [Functor.mapIso_hom]
       rw [FiltQuot.dualHom_map, CategoryTheory.Quotient.lift_map_functor_map,
         CategoryTheory.Quotient.lift_map_functor_map, Functor.comp_map, Functor.comp_map,
         FiltQuot.dualHom_map, ← Functor.map_comp, ← Functor.map_comp, F.ξ_natural]
     ξ_dual M := by
       simp only [Functor.mapIso_hom]
       rw [FiltQuot.dualHom_map, F.ξ_dual, Functor.map_comp, eqToHom_map]
       rfl },
    fun M => by
      obtain ⟨h, hh⟩ := hF M.as
      refine ⟨congrArg (FiltQuot.functor (supp Z')).obj h, ?_⟩
      simp only [Functor.mapIso_hom]
      rw [hh, eqToHom_map],
    CategoryTheory.Quotient.lift_spec _ _ (lift_compat F hZ)⟩

end HSP
