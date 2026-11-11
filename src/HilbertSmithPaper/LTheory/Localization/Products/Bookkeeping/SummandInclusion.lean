import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.ComplexProduct

/-!
# Summand inclusions of a tensor product

For a duality pairing `(⊠, κ)` and complexes `C`, `D` with finitely many nonzero chain objects,
the inclusion `ι_{p,q} : C_p ⊠ D_q → (C ⊗ D)_r` of a summand when `p + q = r`, and `0` otherwise
(Mathlib's `ιMapBifunctorOrZero`).
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

namespace cxProd

variable {C : ChainComplex B ℤ} {D : ChainComplex E ℤ}
  (hC : {r | ¬ IsZero (C.X r)}.Finite) (hD : {r | ¬ IsZero (D.X r)}.Finite)

/-- **Summand inclusions of a tensor product.** The inclusion of the summand `C_p ⊠ D_q` into
`(C ⊗ D)_r` (zero unless `p + q = r`). -/
noncomputable abbrev ι (p q r : ℤ) : P.tensor.obj (C.X p, D.X q) ⟶ (cxProd P C D hC hD).X r :=
  haveI := P.hasMapBifunctor_of_finite hC hD
  HomologicalComplex.ιMapBifunctorOrZero C D (Functor.curry.obj P.tensor) (ComplexShape.down ℤ)
    p q r

end cxProd

end HSP
