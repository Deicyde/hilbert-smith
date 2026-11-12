import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.ProductSumsExist

/-!
# Tensor product of complexes

For a duality pairing `(⊠, κ) : B × E → B''` and chain complexes `C` in `B`, `D` in `E`
(`ChainComplex _ ℤ`, differentials of degree `-1`), each with only finitely many chain objects that
are not zero objects, the tensor product `C ⊗ D` is the complex in `B''` with
`(C ⊗ D)_r = ⨁_{p+q=r} C_p ⊠ D_q` and differential `d ⊠ 1 + (-1)^p 1 ⊠ d` on `C_p ⊠ D_q`.

It is Mathlib's `HomologicalComplex.mapBifunctor` for the curried functor `⊠` and the complex
shape `ComplexShape.down ℤ`, whose total-complex signs are `ε₁ = 1` and `ε₂ (p, q) = (-1)^p`
(`HSP.tensorSignsDownInt`). The direct sums exist by `HSP.DualityPairing.hasMapBifunctor_of_finite`.
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

/-- **Tensor product of complexes.** For complexes `C` in `B` and `D` in `E` with finitely many
nonzero chain objects, `C ⊗ D` has `(C ⊗ D)_r = ⨁_{p+q=r} C_p ⊠ D_q` and differential
`d ⊠ 1 + (-1)^p 1 ⊠ d` on `C_p ⊠ D_q`. -/
noncomputable abbrev cxProd (C : ChainComplex B ℤ) (D : ChainComplex E ℤ)
    (hC : {r | ¬ IsZero (C.X r)}.Finite) (hD : {r | ¬ IsZero (D.X r)}.Finite) :
    ChainComplex B'' ℤ :=
  haveI := P.hasMapBifunctor_of_finite hC hD
  C.mapBifunctor D (Functor.curry.obj P.tensor) (ComplexShape.down ℤ)

end HSP
