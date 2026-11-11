import HilbertSmithPaper.LTheory.Base.Complexes.Functors.FunctorComplex
import HilbertSmithPaper.LTheory.Base.Complexes.DualComplex

/-!
# Duality functors and dual complexes

For a duality functor `(F, ξ) : ℬ → ℬ'` and a complex `C` in `ℬ`, the maps `ξ⁻¹_{C_{k-r}}` form
an isomorphism of complexes `(F C)^{k-*} ≅ F(C^{k-*})`, by naturality of `ξ`.
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

private lemma map_units_smul' {X Y : B} (u : ℤˣ) (f : X ⟶ Y) :
    F.toFunctor.map (u • f) = u • F.toFunctor.map f := by
  rw [Units.smul_def, Units.smul_def, Functor.map_zsmul]

private lemma inv_natural' {M N : B} (f : M ⟶ N) :
    (F.ξ N).inv ≫ F.toFunctor.map (dualHom f) = dualHom (F.toFunctor.map f) ≫ (F.ξ M).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← F.ξ_natural, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- **Duality functors and dual complexes.** The isomorphism `ξ⁻¹ : (F C)^{k-*} ≅ F(C^{k-*})`,
`ξ⁻¹_{C_{k-r}}` in degree `r`. -/
def dualCxIso (C : ChainComplex B ℤ) (k : ℤ) : dualCx (F.mapCx C) k ≅ F.mapCx (dualCx C k) :=
  HomologicalComplex.Hom.isoOfComponents (fun r => (F.ξ (C.X (k - r))).symm) (by
    intro i j _
    simp only [Iso.symm_hom, Functor.mapHomologicalComplex_obj_d, map_units_smul',
      Linear.comp_units_smul, Linear.units_smul_comp, inv_natural'])

end DualFunctor

end HSP
