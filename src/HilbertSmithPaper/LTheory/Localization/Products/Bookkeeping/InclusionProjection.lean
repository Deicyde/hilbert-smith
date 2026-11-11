import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.SummandInclusion
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.SummandProjection

/-!
# Projection after inclusion of the same summand

For a duality pairing `(⊠, κ)`, complexes `C`, `D` with finitely many nonzero chain objects and
`p + q = r`, `π_{p,q} ∘ ι_{p,q} = 1` on `C_p ⊠ D_q`.
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

/-- **Projection after inclusion of the same summand.** -/
@[reassoc]
lemma ι_π_self {p q r : ℤ} (h : p + q = r) : ι P hC hD p q r ≫ π P hC hD p q r = 𝟙 _ := by
  have := P.hasMapBifunctor_of_finite hC hD
  rw [ι, HomologicalComplex.ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ h, π,
    HomologicalComplex.ι_mapBifunctorDesc, dite_eq_left ⟨rfl, rfl⟩, eqToHom_refl]
  rfl

end cxProd

end HSP
