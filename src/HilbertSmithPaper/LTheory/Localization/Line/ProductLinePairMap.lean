import Mathlib
import HilbertSmithPaper.LTheory.Base.Pairs.PairMap
import HilbertSmithPaper.LTheory.Bounded.Categories.IteratedBoundedCategory
import HilbertSmithPaper.LTheory.Localization.Products.BoxPairingPow
import HilbertSmithPaper.LTheory.Localization.Products.ExternalProduct
import HilbertSmithPaper.LTheory.Localization.Products.ProductDualIso
import HilbertSmithPaper.LTheory.Localization.Products.SymmetricLineCycle
import HilbertSmithPaper.LTheory.Localization.Products.SymmetricLineStructure
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.ProductMap
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.SummandInclusion
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.DualComplexFinite
import HilbertSmithPaper.LTheory.Base.Complexes.CycleChainMap

/-!
# The pair map of a product with the line

Let `f : C ⟶ D` carry pair data `(δφ, φ)` in `Kar C_{ℤ^j} A`, with pair map
`ψ : D^{n-*} ⟶ 𝒞(f)`. Let `J : 𝒞(f) ⊗ Λ ≅ 𝒞(f ⊗ 1)` be the isomorphism that is the canonical one
on `D_a ⊠ Λ_b` and `(-1)^b` times the canonical one on `C_{a-1} ⊠ Λ_b`. Then the pair map of
`(f ⊗ 1, δφ ⊗ λ, φ ⊗ λ)` is `J ∘ (ψ ⊗ λ_♮) ∘ Ξ`, with `Ξ` the duality isomorphism of products.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents
open scoped CategoryTheory.Prod

namespace HSP

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]

/-- **The pair map of a product with the line.** For pair data `(f, δφ, φ)` with pair map `ψ`,
the pair map of `(f ⊗ 1, δφ ⊗ λ, φ ⊗ λ)` is `J ∘ (ψ ⊗ λ_♮) ∘ Ξ`, where
`J : 𝒞(f) ⊗ Λ ≅ 𝒞(f ⊗ 1)` is the canonical map on `D_a ⊠ Λ_b` and `(-1)^b` times the canonical
map on `C_{a-1} ⊠ Λ_b`. -/
theorem pairMap_prod_line {j : ℕ} {C D : ChainComplex (Karoubi (BoundedPow A j)) ℤ} (f : C ⟶ D)
    {m n : ℤ} (hmn : m + 1 = n) (δφ : (StructureCx D).X n) (φ : (StructureCx C).X m)
    (hφ : (StructureCx C).d m (m - 1) φ = 0)
    (hδφ : (StructureCx D).d n m δφ = (StructureCx.push f).f m φ)
    (hC : {r | ¬ IsZero (C.X r)}.Finite) (hD : {r | ¬ IsZero (D.X r)}.Finite)
    (hK : {r | ¬ IsZero ((cone f).X r)}.Finite) (hΛ : {r | ¬ IsZero (symLine.X r)}.Finite)
    (hφ' : (StructureCx (cxProd (boxPairingPow A j) C symLine hC hΛ)).d (m + 1) (m + 1 - 1)
      (strProd (boxPairingPow A j) hC hΛ φ symLine.str (m + 1) rfl) = 0)
    (hδφ' : (StructureCx (cxProd (boxPairingPow A j) D symLine hD hΛ)).d (n + 1) (m + 1)
      (strProd (boxPairingPow A j) hD hΛ δφ symLine.str (n + 1) rfl) =
      (StructureCx.push (cxProdMap (boxPairingPow A j) f (𝟙 symLine) hC hΛ hD hΛ)).f (m + 1)
        (strProd (boxPairingPow A j) hC hΛ φ symLine.str (m + 1) rfl)) :
    ∃ J : cxProd (boxPairingPow A j) (cone f) symLine hK hΛ ≅
        cone (cxProdMap (boxPairingPow A j) f (𝟙 symLine) hC hΛ hD hΛ),
      (∀ a b r (h : a + b = r), cxProd.ι (boxPairingPow A j) hK hΛ a b r ≫ J.hom.f r =
        (boxPairingPow A j).tensor.map (biprod.fst ×ₘ 𝟙 (symLine.X b)) ≫
            cxProd.ι (boxPairingPow A j) hD hΛ a b r ≫ biprod.inl +
          b.negOnePow • ((boxPairingPow A j).tensor.map (biprod.snd ×ₘ 𝟙 (symLine.X b)) ≫
            cxProd.ι (boxPairingPow A j) hC hΛ (a - 1) b (r - 1) ≫ biprod.inr)) ∧
      pairMap (cxProdMap (boxPairingPow A j) f (𝟙 symLine) hC hΛ hD hΛ) (by omega)
          (strProd (boxPairingPow A j) hD hΛ δφ symLine.str (n + 1) rfl)
          (strProd (boxPairingPow A j) hC hΛ φ symLine.str (m + 1) rfl) hφ' hδφ' =
        (prodDualIso (boxPairingPow A j) hD hΛ n 1 (n + 1) rfl).hom ≫
          cxProdMap (boxPairingPow A j) (pairMap f hmn δφ φ hφ hδφ)
            (StructureCx.toHom symLine.str symLine.str_T_and_cycle.2)
            (dualCx_finite hD n) (dualCx_finite hΛ 1) hK hΛ ≫ J.hom := by
  sorry

end HSP
