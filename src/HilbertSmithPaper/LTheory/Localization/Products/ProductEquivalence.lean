import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.ComplexProduct

/-!
# Tensor products of equivalences

For a duality pairing `(⊠, κ)`, if `f : C ⟶ C'` and `g : D ⟶ D'` are chain homotopy equivalences
(of complexes with finitely many nonzero chain objects), then `f ⊗ g` is one. A homotopy
`h : f ≃ f'` gives `f ⊗ g ≃ f' ⊗ g`, and one `g ≃ g'` gives `f ⊗ g ≃ f ⊗ g'` (Mathlib's
`mapBifunctorMapHomotopy₁`, `mapBifunctorMapHomotopy₂`); apply them to the composites with the
homotopy inverses, using `(f' ⊗ g') (f ⊗ g) = f' f ⊗ g' g`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Prod

namespace HSP

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {B : Type u₁} [Category.{v₁} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]
  {E : Type u₂} [Category.{v₂} E] [Preadditive E] [Linear ℚ E] [HasFiniteBiproducts E]
  [DualCat E]
  {B'' : Type u₃} [Category.{v₃} B''] [Preadditive B''] [Linear ℚ B''] [HasFiniteBiproducts B'']
  [DualCat B'']
  (P : DualityPairing B E B'')

/-- Functoriality of `⊗` on chain maps. -/
private lemma cxProdMap_comp {C C' C'' : ChainComplex B ℤ} {D D' D'' : ChainComplex E ℤ}
    (f : C ⟶ C') (f' : C' ⟶ C'') (g : D ⟶ D') (g' : D' ⟶ D'')
    (hC : {r | ¬ IsZero (C.X r)}.Finite) (hD : {r | ¬ IsZero (D.X r)}.Finite)
    (hC' : {r | ¬ IsZero (C'.X r)}.Finite) (hD' : {r | ¬ IsZero (D'.X r)}.Finite)
    (hC'' : {r | ¬ IsZero (C''.X r)}.Finite) (hD'' : {r | ¬ IsZero (D''.X r)}.Finite) :
    cxProdMap P (f ≫ f') (g ≫ g') hC hD hC'' hD'' =
      cxProdMap P f g hC hD hC' hD' ≫ cxProdMap P f' g' hC' hD' hC'' hD'' := by
  have := P.hasMapBifunctor_of_finite hC hD
  have := P.hasMapBifunctor_of_finite hC' hD'
  have := P.hasMapBifunctor_of_finite hC'' hD''
  ext j p q h
  simp only [HomologicalComplex.comp_f, HomologicalComplex.ι_mapBifunctorMap,
    HomologicalComplex.ι_mapBifunctorMap_assoc, Functor.curry_obj_map_app,
    Functor.curry_obj_obj_map, ← Functor.map_comp_assoc, CategoryTheory.prod_comp,
    Category.id_comp, Category.comp_id]

private lemma cxProdMap_id {C : ChainComplex B ℤ} {D : ChainComplex E ℤ}
    (hC : {r | ¬ IsZero (C.X r)}.Finite) (hD : {r | ¬ IsZero (D.X r)}.Finite) :
    cxProdMap P (𝟙 C) (𝟙 D) hC hD hC hD = 𝟙 _ := by
  have := P.hasMapBifunctor_of_finite hC hD
  ext j p q h
  simp

/-- **Tensor products of equivalences.** If `f` and `g` are chain homotopy equivalences, so is
`f ⊗ g`. -/
theorem cxProd_homotopyEquiv {C C' : ChainComplex B ℤ} {D D' : ChainComplex E ℤ}
    {f : C ⟶ C'} {g : D ⟶ D'} (hf : ∃ e : HomotopyEquiv C C', e.hom = f)
    (hg : ∃ e : HomotopyEquiv D D', e.hom = g)
    (hC : {r | ¬ IsZero (C.X r)}.Finite) (hD : {r | ¬ IsZero (D.X r)}.Finite)
    (hC' : {r | ¬ IsZero (C'.X r)}.Finite) (hD' : {r | ¬ IsZero (D'.X r)}.Finite) :
    ∃ e : HomotopyEquiv (cxProd P C D hC hD) (cxProd P C' D' hC' hD'),
      e.hom = cxProdMap P f g hC hD hC' hD' := by
  obtain ⟨e₁, rfl⟩ := hf
  obtain ⟨e₂, rfl⟩ := hg
  have := P.hasMapBifunctor_of_finite hC hD
  have := P.hasMapBifunctor_of_finite hC' hD'
  let F := Functor.curry.obj P.tensor
  refine ⟨{ hom := cxProdMap P e₁.hom e₂.hom hC hD hC' hD'
            inv := cxProdMap P e₁.inv e₂.inv hC' hD' hC hD
            homotopyHomInvId := ?_
            homotopyInvHomId := ?_ }, rfl⟩
  · rw [← cxProdMap_comp, ← cxProdMap_id P hC hD]
    exact (HomologicalComplex.mapBifunctorMapHomotopy₁ e₁.homotopyHomInvId _ F _).trans
      (HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 C) e₂.homotopyHomInvId F _)
  · rw [← cxProdMap_comp, ← cxProdMap_id P hC' hD']
    exact (HomologicalComplex.mapBifunctorMapHomotopy₁ e₁.homotopyInvHomId _ F _).trans
      (HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 C') e₂.homotopyInvHomId F _)

end HSP
