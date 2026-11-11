import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.ExternalProduct

/-!
# Leibniz rule for products

`∂(φ ⊗ θ) = ∂φ ⊗ θ + (-1)^m φ ⊗ ∂θ` for `φ ∈ M(C)_m`, `θ ∈ M(D)_n`. The degrees are written with
a parameter `k = m + n`, so the three products live in `M(C ⊗ D)_{k-1}` without transports.
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

/-- **Leibniz rule for products.** `∂(φ ⊗ θ) = ∂φ ⊗ θ + (-1)^m φ ⊗ ∂θ`. -/
theorem strProd_boundary (P : DualityPairing B E B'') {C : ChainComplex B ℤ}
    {D : ChainComplex E ℤ} (hC : {r | ¬ IsZero (C.X r)}.Finite)
    (hD : {r | ¬ IsZero (D.X r)}.Finite) {m n : ℤ} (φ : (StructureCx C).X m)
    (θ : (StructureCx D).X n) (k : ℤ) (hk : m + n = k) :
    (StructureCx (cxProd P C D hC hD)).d k (k - 1) (strProd P hC hD φ θ k hk) =
      strProd P hC hD ((StructureCx C).d m (m - 1) φ) θ (k - 1) (by omega) +
        m.negOnePow • strProd P hC hD φ ((StructureCx D).d n (n - 1) θ) (k - 1) (by omega) := by
  sorry

end HSP
