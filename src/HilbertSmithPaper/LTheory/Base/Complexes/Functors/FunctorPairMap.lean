import HilbertSmithPaper.LTheory.Base.Complexes.FunctorPush
import HilbertSmithPaper.LTheory.Base.Complexes.Functors.FunctorCone
import HilbertSmithPaper.LTheory.Base.Pairs.PairMap
import HilbertSmithPaper.LTheory.Base.Complexes.Functors.FunctorStructureLaws

/-!
# Duality functors and pair maps

For a duality functor `(F, ξ) : B → B'`, the pair map of the image `(F f, F_% δφ, F_% φ)` of
pair data is `κ ∘ F(ψ) ∘ ξ⁻¹`, with `κ : F(𝒞(f)) ≅ 𝒞(F f)` and `ξ⁻¹ : (F D)^{n-*} ≅ F(D^{n-*})`.
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

private lemma map_units_smul'' {X Y : B} (u : ℤˣ) (f : X ⟶ Y) :
    F.toFunctor.map (u • f) = u • F.toFunctor.map f := by
  rw [Units.smul_def, Units.smul_def, Functor.map_zsmul]

private lemma inv_natural'' {M N : B} (f : M ⟶ N) :
    (F.ξ N).inv ≫ F.toFunctor.map (dualHom f) = dualHom (F.toFunctor.map f) ≫ (F.ξ M).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← F.ξ_natural, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- **Duality functors and pair maps.** The images satisfy the conditions of pair data for `F f`,
and the pair map of the image is `κ ∘ F(ψ) ∘ ξ⁻¹`. -/
lemma pairMap_map {C D : ChainComplex B ℤ} (f : C ⟶ D) {m n : ℤ} (hmn : m + 1 = n)
    (δφ : (StructureCx D).X n) (φ : (StructureCx C).X m)
    (hφ : (StructureCx C).d m (m - 1) φ = 0)
    (hδφ : (StructureCx D).d n m δφ = (StructureCx.push f).f m φ) :
    pairMap ((F.toFunctor.mapHomologicalComplex _).map f) hmn (F.mapStructure D n δφ)
        (F.mapStructure C m φ) (by rw [F.mapStructure_compat.1, hφ, map_zero])
        (by rw [F.mapStructure_compat.1, hδφ, F.mapStructure_pushforward]) =
      (F.dualCxIso D n).hom ≫
        (F.toFunctor.mapHomologicalComplex _).map (pairMap f hmn δφ φ hφ hδφ) ≫
          (F.mapConeIso f).hom := by
  refine HomologicalComplex.hom_ext _ _ fun r => ?_
  change biprod.lift _ _ = (F.ξ (D.X (n - r))).inv ≫ F.toFunctor.map (biprod.lift _ _) ≫
    biprod.lift (F.toFunctor.map (biprod.fst : D.X r ⊞ C.X (r - 1) ⟶ _))
      (F.toFunctor.map (biprod.snd : D.X r ⊞ C.X (r - 1) ⟶ _))
  apply biprod.hom_ext
  · simp only [biprod.lift_fst, Category.assoc, ← Functor.map_comp]
    rfl
  · simp only [Category.assoc, biprod.lift_snd]
    rw [← F.toFunctor.map_comp, biprod.lift_snd, map_units_smul'', Linear.comp_units_smul,
      F.toFunctor.map_comp,
      ← Category.assoc (F.ξ (D.X (n - r))).inv, inv_natural'', Category.assoc]
    rfl

end DualFunctor

end HSP
