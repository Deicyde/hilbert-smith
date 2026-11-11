import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.ExternalProduct
import HilbertSmithPaper.LTheory.Localization.Products.ProductDualIso
import HilbertSmithPaper.LTheory.Base.Complexes.CycleChainMap

/-!
# Duality map of a product

For cycles `φ ∈ M(C)_m` and `θ ∈ M(D)_n`, `(φ ⊗ θ)_♮ = (φ_♮ ⊗ θ_♮) ∘ Ξ`, where `Ξ` is the
isomorphism `(C ⊗ D)^{k-*} ≅ C^{m-*} ⊗ D^{n-*}` (`k = m + n`). The duality map `(φ ⊗ θ)_♮` needs
`φ ⊗ θ` to be a cycle, which the Leibniz rule gives; the statement takes that as the hypothesis
`hφθ` (any proof).
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

/-- **Duality map of a product.** `(φ ⊗ θ)_♮ = (φ_♮ ⊗ θ_♮) ∘ Ξ` for cycles `φ`, `θ`. -/
theorem strProd_toHom (P : DualityPairing B E B'') {C : ChainComplex B ℤ}
    {D : ChainComplex E ℤ} (hC : {r | ¬ IsZero (C.X r)}.Finite)
    (hD : {r | ¬ IsZero (D.X r)}.Finite) {m n : ℤ} (φ : (StructureCx C).X m)
    (θ : (StructureCx D).X n) (hφ : (StructureCx C).d m (m - 1) φ = 0)
    (hθ : (StructureCx D).d n (n - 1) θ = 0) (k : ℤ) (hk : m + n = k)
    (hφθ : (StructureCx (cxProd P C D hC hD)).d k (k - 1) (strProd P hC hD φ θ k hk) = 0) :
    StructureCx.toHom (strProd P hC hD φ θ k hk) hφθ =
      (prodDualIso P hC hD m n k hk).hom ≫
        cxProdMap P (StructureCx.toHom φ hφ) (StructureCx.toHom θ hθ) (dualCx_finite hC m)
          (dualCx_finite hD n) hC hD := by
  sorry

end HSP
