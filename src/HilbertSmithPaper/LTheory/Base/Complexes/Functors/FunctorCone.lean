import HilbertSmithPaper.LTheory.Base.Complexes.Functors.FunctorComplex
import HilbertSmithPaper.LTheory.Base.Complexes.Cone
import HilbertSmithPaper.LTheory.Base.Complexes.DualComplex

/-!
# Duality functors and mapping cones

For a duality functor `(F, ξ) : B → B'` and a chain map `f : C ⟶ D`, the maps
`F(D_r ⊞ C_{r-1}) ≅ F D_r ⊞ F C_{r-1}` form an isomorphism of complexes `F(𝒞(f)) ≅ 𝒞(F f)`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v₁ v₂ u₁ u₂

variable {B : Type u₁} [Category.{v₁} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]
  {B' : Type u₂} [Category.{v₂} B'] [Preadditive B'] [Linear ℚ B'] [HasFiniteBiproducts B']
  [DualCat B']

namespace DualFunctor

variable (F : DualFunctor B B')

/-- `F(X ⊞ Y) ≅ F X ⊞ F Y` for the additive functor `F`. -/
private noncomputable def biprodIso (X Y : B) :
    F.toFunctor.obj (X ⊞ Y) ≅ F.toFunctor.obj X ⊞ F.toFunctor.obj Y where
  hom := biprod.lift (F.toFunctor.map biprod.fst) (F.toFunctor.map biprod.snd)
  inv := biprod.desc (F.toFunctor.map biprod.inl) (F.toFunctor.map biprod.inr)
  hom_inv_id := by
    rw [biprod.lift_desc, ← F.toFunctor.map_comp, ← F.toFunctor.map_comp, ← F.toFunctor.map_add,
      biprod.total, F.toFunctor.map_id]
  inv_hom_id := by
    apply biprod.hom_ext <;> apply biprod.hom_ext' <;>
      simp [← F.toFunctor.map_comp]

/-- **Duality functors and mapping cones.** The canonical isomorphism `κ : F(𝒞(f)) ≅ 𝒞(F f)`, `F(D_r ⊞ C_{r-1}) ≅ F D_r ⊞ F C_{r-1}`. -/
noncomputable def mapConeIso {C D : ChainComplex B ℤ} (f : C ⟶ D) :
    F.mapCx (cone f) ≅ cone ((F.toFunctor.mapHomologicalComplex _).map f) :=
  HomologicalComplex.Hom.isoOfComponents (fun r => biprodIso F (D.X r) (C.X (r - 1)))
    (by
      intro i j hij
      simp only [ComplexShape.down_Rel] at hij
      obtain rfl : j = i - 1 := by omega
      simp only [Functor.mapHomologicalComplex_obj_d]
      change _ ≫ cone.d _ i (i - 1) = F.toFunctor.map (cone.d f i (i - 1)) ≫ _
      simp only [cone.d, dite_true, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
        Category.comp_id, biprodIso]
      apply biprod.hom_ext
      · simp [Preadditive.comp_add, ← Functor.map_comp]
      · simp [← Functor.map_comp])

end DualFunctor

end HSP
