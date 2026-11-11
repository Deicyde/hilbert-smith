import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.ComplexProduct

/-!
# Tensor product of chain maps

For a duality pairing `(⊠, κ) : B × E → B''` and chain maps `f : C ⟶ C'`, `g : D ⟶ D'` of
complexes with finitely many nonzero chain objects, the chain map `f ⊗ g : C ⊗ D ⟶ C' ⊗ D'` is
`f_p ⊠ g_q` on `C_p ⊠ D_q` (Mathlib's `mapBifunctorMap`).
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {B : Type u₁} [Category.{v₁} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]
  {E : Type u₂} [Category.{v₂} E] [Preadditive E] [Linear ℚ E] [HasFiniteBiproducts E]
  [DualCat E]
  {B'' : Type u₃} [Category.{v₃} B''] [Preadditive B''] [Linear ℚ B''] [HasFiniteBiproducts B'']
  [DualCat B'']
  (P : DualityPairing B E B'')

/-- **Tensor product of chain maps.** The chain map `f ⊗ g : C ⊗ D ⟶ C' ⊗ D'`, equal to
`f_p ⊠ g_q` on `C_p ⊠ D_q`. -/
noncomputable abbrev cxProdMap {C C' : ChainComplex B ℤ} {D D' : ChainComplex E ℤ}
    (f : C ⟶ C') (g : D ⟶ D') (hC : {r | ¬ IsZero (C.X r)}.Finite)
    (hD : {r | ¬ IsZero (D.X r)}.Finite) (hC' : {r | ¬ IsZero (C'.X r)}.Finite)
    (hD' : {r | ¬ IsZero (D'.X r)}.Finite) :
    cxProd P C D hC hD ⟶ cxProd P C' D' hC' hD' :=
  haveI := P.hasMapBifunctor_of_finite hC hD
  haveI := P.hasMapBifunctor_of_finite hC' hD'
  HomologicalComplex.mapBifunctorMap f g (Functor.curry.obj P.tensor) (ComplexShape.down ℤ)

end HSP
