import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.ProductMap

/-!
# Tensor products of chain maps compose

For a duality pairing `(⊠, κ)` and chain maps `f : C ⟶ C'`, `f' : C' ⟶ C''`, `g : D ⟶ D'`,
`g' : D' ⟶ D''` of complexes with finitely many nonzero chain objects,
`(f' ∘ f) ⊗ (g' ∘ g) = (f' ⊗ g') ∘ (f ⊗ g)`.
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

/-- **Tensor products of chain maps compose.** -/
lemma cxProdMap_comp {C C' C'' : ChainComplex B ℤ} {D D' D'' : ChainComplex E ℤ}
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

end HSP
