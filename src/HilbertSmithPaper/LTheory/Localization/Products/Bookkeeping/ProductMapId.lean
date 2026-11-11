import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.ProductMap

/-!
# Tensor product of identities

For a duality pairing `(⊠, κ)` and complexes `C`, `D` with finitely many nonzero chain objects,
`1_C ⊗ 1_D = 1_{C ⊗ D}`.
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

/-- **Tensor product of identities.** -/
lemma cxProdMap_id {C : ChainComplex B ℤ} {D : ChainComplex E ℤ}
    (hC : {r | ¬ IsZero (C.X r)}.Finite) (hD : {r | ¬ IsZero (D.X r)}.Finite) :
    cxProdMap P (𝟙 C) (𝟙 D) hC hD hC hD = 𝟙 _ := by
  have := P.hasMapBifunctor_of_finite hC hD
  ext j p q h
  simp

end HSP
