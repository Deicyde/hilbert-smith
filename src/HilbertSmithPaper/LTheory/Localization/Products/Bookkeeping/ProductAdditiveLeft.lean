import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.ExternalProduct

/-!
# External products are additive in the first structure

For a duality pairing `(⊠, κ)`, complexes `C`, `D` with finitely many nonzero chain objects,
`φ, φ' ∈ M(C)_m` and `θ ∈ M(D)_n`, `(φ + φ') ⊗ θ = φ ⊗ θ + φ' ⊗ θ`: every block of the external
product is additive in `φ`, `⊠` being additive in the first variable.
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

/-- **External products are additive in the first structure.**
`(φ + φ') ⊗ θ = φ ⊗ θ + φ' ⊗ θ`. -/
lemma strProd_add_left (P : DualityPairing B E B'') {C : ChainComplex B ℤ}
    {D : ChainComplex E ℤ} (hC : {r | ¬ IsZero (C.X r)}.Finite)
    (hD : {r | ¬ IsZero (D.X r)}.Finite) {m n : ℤ} (φ φ' : (StructureCx C).X m)
    (θ : (StructureCx D).X n) (k : ℤ) (hk : m + n = k) :
    strProd P hC hD (φ + φ') θ k hk = strProd P hC hD φ θ k hk + strProd P hC hD φ' θ k hk := by
  funext x
  show strProd P hC hD (φ + φ') θ k hk x =
    strProd P hC hD φ θ k hk x + strProd P hC hD φ' θ k hk x
  simp only [strProd, Pi.add_apply, P.map_add_left, Preadditive.add_comp, Preadditive.comp_add,
    smul_add, Finset.sum_add_distrib]

end HSP
