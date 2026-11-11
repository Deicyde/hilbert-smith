import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.DualityPairing
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.ProductSupport

/-!
# Summands outside the support vanish

For a duality pairing `(⊠, κ) : B × E → B''` and complexes `C`, `D` with finitely many nonzero
chain objects, if `p + q = r` and `(p, q)` is not in the support of degree `r`, then `C_p ⊠ D_q`
is a zero object: one of `C_p`, `D_q` is, and `⊠` is additive in each variable.
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

private lemma isZero_tensor_left {N : B} (hN : IsZero N) (V : E) :
    IsZero (P.tensor.obj (N, V)) := by
  rw [IsZero.iff_id_eq_zero] at hN ⊢
  rw [← P.tensor.map_id, show 𝟙 (N, V) = 𝟙 N ×ₘ 𝟙 V from rfl, hN]
  simpa using P.map_smul_left 0 (0 : N ⟶ N) (𝟙 V)

private lemma isZero_tensor_right (N : B) {V : E} (hV : IsZero V) :
    IsZero (P.tensor.obj (N, V)) := by
  rw [IsZero.iff_id_eq_zero] at hV ⊢
  rw [← P.tensor.map_id, show 𝟙 (N, V) = 𝟙 N ×ₘ 𝟙 V from rfl, hV]
  simpa using P.map_smul_right 0 (𝟙 N) (0 : V ⟶ V)

namespace cxProd

variable {C : ChainComplex B ℤ} {D : ChainComplex E ℤ}
  (hC : {r | ¬ IsZero (C.X r)}.Finite) (hD : {r | ¬ IsZero (D.X r)}.Finite)

/-- **Summands outside the support vanish.** -/
lemma isZero_of_not_mem_supp {p q r : ℤ} (h : p + q = r) (hx : (p, q) ∉ supp hC hD r) :
    IsZero (P.tensor.obj (C.X p, D.X q)) := by
  rw [mem_supp] at hx
  by_cases hp : IsZero (C.X p)
  · exact isZero_tensor_left P hp _
  · by_cases hq : IsZero (D.X q)
    · exact isZero_tensor_right P _ hq
    · exact absurd ⟨⟨hp, hq⟩, h⟩ hx

end cxProd

end HSP
