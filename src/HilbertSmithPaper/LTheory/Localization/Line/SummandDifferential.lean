import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.SummandInclusion

/-!
# Differential of a tensor product on a summand

For a duality pairing `(⊠, κ)` and complexes `C`, `D` with finitely many nonzero chain objects,
the inclusion of the summand `C_p ⊠ D_q` followed by the differential of `C ⊗ D` is
`d ι_{p,q} = ι_{p-1,q} (d ⊠ 1) + (-1)^p ι_{p,q-1} (1 ⊠ d)`.
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

namespace cxProd

variable {C : ChainComplex B ℤ} {D : ChainComplex E ℤ}
  (hC : {r | ¬ IsZero (C.X r)}.Finite) (hD : {r | ¬ IsZero (D.X r)}.Finite)

/-- **Differential of a tensor product on a summand.**
`ι_{p,q} ≫ d = (d ⊠ 1) ≫ ι_{p-1,q} + (-1)^p (1 ⊠ d) ≫ ι_{p,q-1}` (with `p' = p - 1`, `q' = q - 1`). -/
lemma ι_d {p q r r' p' q' : ℤ} (h : p + q = r) (hp : p' + 1 = p)
    (hq : q' + 1 = q) :
    ι P hC hD p q r ≫ (cxProd P C D hC hD).d r r' =
      P.tensor.map (C.d p p' ×ₘ 𝟙 (D.X q)) ≫ ι P hC hD p' q r' +
        p.negOnePow • (P.tensor.map (𝟙 (C.X p) ×ₘ D.d q q') ≫ ι P hC hD p q' r') := by
  have := P.hasMapBifunctor_of_finite hC hD
  have hp' : (ComplexShape.down ℤ).Rel p p' := hp
  have hq' : (ComplexShape.down ℤ).Rel q q' := hq
  rw [ι, HomologicalComplex.ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ h,
    HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
    HomologicalComplex.mapBifunctor.d₁_eq' _ _ _ _ hp',
    HomologicalComplex.mapBifunctor.d₂_eq' _ _ _ _ _ hq']
  have e1 : ComplexShape.ε₁ (ComplexShape.down ℤ) (ComplexShape.down ℤ) (ComplexShape.down ℤ)
      (p, q) = 1 := rfl
  have e2 : ComplexShape.ε₂ (ComplexShape.down ℤ) (ComplexShape.down ℤ) (ComplexShape.down ℤ)
      (p, q) = p.negOnePow := rfl
  rw [e1, e2, one_smul]
  rfl

end cxProd

end HSP
