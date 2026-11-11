import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.SummandInclusion
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.SummandProjection

/-!
# Projection after inclusion of another summand

For a duality pairing `(⊠, κ)`, complexes `C`, `D` with finitely many nonzero chain objects and
`(p, q) ≠ (p', q')`, `π_{p',q'} ∘ ι_{p,q} = 0` from `C_p ⊠ D_q` to `C_{p'} ⊠ D_{q'}`.
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

/-- **Projection after inclusion of another summand.** -/
@[reassoc]
lemma ι_π_of_ne {p q p' q' r : ℤ} (hne : ¬ (p = p' ∧ q = q')) :
    ι P hC hD p q r ≫ π P hC hD p' q' r = 0 := by
  have := P.hasMapBifunctor_of_finite hC hD
  by_cases h : p + q = r
  · rw [ι, HomologicalComplex.ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ h, π,
      HomologicalComplex.ι_mapBifunctorDesc, dite_eq_right hne]
  · rw [ι, HomologicalComplex.ιMapBifunctorOrZero_eq_zero _ _ _ _ _ _ _ h, zero_comp]

end cxProd

end HSP
