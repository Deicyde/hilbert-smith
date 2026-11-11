import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.ExternalProduct
import HilbertSmithPaper.LTheory.Base.Complexes.StructureInvolution

/-!
# Products commute with T

`T(φ ⊗ θ) = Tφ ⊗ Tθ` for `φ ∈ M(C)_m`, `θ ∈ M(D)_n`.
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

/-- **Products commute with T.** `T(φ ⊗ θ) = Tφ ⊗ Tθ`. -/
theorem strProd_T (P : DualityPairing B E B'') {C : ChainComplex B ℤ}
    {D : ChainComplex E ℤ} (hC : {r | ¬ IsZero (C.X r)}.Finite)
    (hD : {r | ¬ IsZero (D.X r)}.Finite) {m n : ℤ} (φ : (StructureCx C).X m)
    (θ : (StructureCx D).X n) (k : ℤ) (hk : m + n = k) :
    (StructureCx.T (cxProd P C D hC hD)).f k (strProd P hC hD φ θ k hk) =
      strProd P hC hD ((StructureCx.T C).f m φ) ((StructureCx.T D).f n θ) k hk := by
  sorry

end HSP
