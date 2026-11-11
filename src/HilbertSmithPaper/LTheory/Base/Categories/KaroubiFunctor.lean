import HilbertSmithPaper.LTheory.Base.Categories.KaroubiDuality

/-!
# Completion of a duality functor

A duality functor `(F, ξ) : A → B` induces `Kar F : Kar A → Kar B`, `(M, e) ↦ (F M, F e)`,
`f ↦ F f` (Mathlib's `functorExtension₂`), with duality isomorphism
`ξ_{(M,e)} = ξ_M ∘ F (e^*) : (F (M^*), F (e^*)) → ((F M)^*, (F e)^*)`, whose inverse is
`F (e^*) ∘ ξ_M⁻¹`. It is strict if `F` is.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

namespace HSP

open DualCat

universe v₁ v₂ u₁ u₂

variable {A : Type u₁} [Category.{v₁} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]
  {B : Type u₂} [Category.{v₂} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

namespace DualFunctor

variable (F : DualFunctor A B)

instance instAdditiveKar : ((functorExtension₂ A B).obj F.toFunctor).Additive where
  map_add {_ _ f g} := Idempotents.Karoubi.hom_ext _ _ (F.toFunctor.map_add (f := f.f) (g := g.f))

instance instLinearKar : ((functorExtension₂ A B).obj F.toFunctor).Linear ℚ where
  map_smul f c := Idempotents.Karoubi.hom_ext _ _ (Functor.Linear.map_smul (F := F.toFunctor) f.f c)

private lemma inv_natural {M N : A} (f : M ⟶ N) :
    (F.ξ N).inv ≫ F.toFunctor.map (dualHom f) = dualHom (F.toFunctor.map f) ≫ (F.ξ M).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← F.ξ_natural, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- The duality isomorphism of `Kar F` at `(M, e)`: `ξ_M ∘ F (e^*)`. -/
private def karξ (P : Karoubi A) :
    ((functorExtension₂ A B).obj F.toFunctor).obj (dual P) ≅
      dual (((functorExtension₂ A B).obj F.toFunctor).obj P) where
  hom := ⟨F.toFunctor.map (dualHom P.p) ≫ (F.ξ P.X).hom, by
    change F.toFunctor.map (dualHom P.p) ≫ (F.toFunctor.map (dualHom P.p) ≫ (F.ξ P.X).hom) ≫
      dualHom (F.toFunctor.map P.p) = _
    rw [Category.assoc, ← F.ξ_natural, ← Category.assoc, ← Category.assoc, ← F.toFunctor.map_comp,
      ← F.toFunctor.map_comp, ← dualHom_comp, ← dualHom_comp, P.idem, P.idem]
    rfl⟩
  inv := ⟨(F.ξ P.X).inv ≫ F.toFunctor.map (dualHom P.p), by
    change dualHom (F.toFunctor.map P.p) ≫ ((F.ξ P.X).inv ≫ F.toFunctor.map (dualHom P.p)) ≫
      F.toFunctor.map (dualHom P.p) = _
    rw [Category.assoc, ← F.toFunctor.map_comp, ← dualHom_comp, P.idem,
      ← Category.assoc, ← inv_natural, Category.assoc, ← F.toFunctor.map_comp, ← dualHom_comp,
      P.idem]
    rfl⟩
  hom_inv_id := by
    ext
    change (F.toFunctor.map (dualHom P.p) ≫ (F.ξ P.X).hom) ≫ (F.ξ P.X).inv ≫
      F.toFunctor.map (dualHom P.p) = F.toFunctor.map (dualHom P.p)
    rw [Category.assoc, Iso.hom_inv_id_assoc, ← F.toFunctor.map_comp, ← dualHom_comp, P.idem]
  inv_hom_id := by
    ext
    change ((F.ξ P.X).inv ≫ F.toFunctor.map (dualHom P.p)) ≫ F.toFunctor.map (dualHom P.p) ≫
      (F.ξ P.X).hom = dualHom (F.toFunctor.map P.p)
    rw [Category.assoc, ← Category.assoc (F.toFunctor.map _), ← F.toFunctor.map_comp,
      ← dualHom_comp, P.idem, F.ξ_natural, Iso.inv_hom_id_assoc]

/-- The completion `Kar F : Kar A → Kar B` of a duality functor, `(M, e) ↦ (F M, F e)`, with
duality isomorphism `ξ_{(M,e)} = ξ_M ∘ F (e^*)`. -/
def kar : DualFunctor (Karoubi A) (Karoubi B) where
  toFunctor := (functorExtension₂ A B).obj F.toFunctor
  ξ := karξ F
  ξ_natural {P Q} f := by
    apply Idempotents.Karoubi.hom_ext
    change F.toFunctor.map (dualHom f.f) ≫ (F.toFunctor.map (dualHom P.p) ≫ (F.ξ P.X).hom) =
      (F.toFunctor.map (dualHom Q.p) ≫ (F.ξ Q.X).hom) ≫ dualHom (F.toFunctor.map f.f)
    rw [← Category.assoc, ← F.toFunctor.map_comp, ← dualHom_comp, Idempotents.Karoubi.p_comp,
      F.ξ_natural, F.ξ_natural, Category.assoc, ← dualHom_comp, ← F.toFunctor.map_comp,
      Idempotents.Karoubi.comp_p]
  ξ_dual P := by
    apply Idempotents.Karoubi.hom_ext
    have hp : F.toFunctor.map P.p ≫ F.toFunctor.map P.p = F.toFunctor.map P.p := by
      rw [← F.toFunctor.map_comp, P.idem]
    have hp' {Z : B} (g : F.toFunctor.obj P.X ⟶ Z) :
        F.toFunctor.map P.p ≫ F.toFunctor.map P.p ≫ g = F.toFunctor.map P.p ≫ g := by
      rw [← Category.assoc, hp]
    change dualHom (F.toFunctor.map (dualHom P.p) ≫ (F.ξ P.X).hom) = _ ≫
      (F.toFunctor.map (dualHom (dualHom P.p)) ≫ (F.ξ (dual P.X)).hom)
    rw [dualHom_comp, F.ξ_dual, Category.assoc, ← F.ξ_natural (dualHom P.p)]
    rw [Idempotents.Karoubi.eqToHom_f, HSP.Karoubi.dual_p, HSP.Karoubi.dual_p]
    have h₀ : dual (dual (F.toFunctor.obj P.X)) = F.toFunctor.obj (dual (dual P.X)) := by simp
    show eqToHom h₀ ≫ F.toFunctor.map (dualHom (dualHom P.p)) ≫ (F.ξ (dual P.X)).hom =
      (dualHom (dualHom (F.toFunctor.map P.p)) ≫ eqToHom h₀) ≫
        F.toFunctor.map (dualHom (dualHom P.p)) ≫ (F.ξ (dual P.X)).hom
    simp [dualHom_dualHom, eqToHom_map, hp']

/-- The completion of a strict duality functor is strict. -/
theorem kar_isStrict (hF : F.IsStrict) : F.kar.IsStrict := by
  intro P
  obtain ⟨h, hξ⟩ := hF P.X
  have hP : F.kar.toFunctor.obj (dual P) = dual (F.kar.toFunctor.obj P) :=
    Idempotents.Karoubi.ext h (by
      change F.toFunctor.map (dualHom P.p) ≫ eqToHom h = eqToHom h ≫ dualHom (F.toFunctor.map P.p)
      rw [← hξ, F.ξ_natural])
  refine ⟨hP, Idempotents.Karoubi.hom_ext _ _ ?_⟩
  change F.toFunctor.map (dualHom P.p) ≫ (F.ξ P.X).hom = _
  rw [hξ, Idempotents.Karoubi.eqToHom_f]
  rfl

end DualFunctor

end HSP
