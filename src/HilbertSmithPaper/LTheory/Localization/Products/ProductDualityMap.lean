import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.ExternalProduct
import HilbertSmithPaper.LTheory.Localization.Products.ProductDualIso
import HilbertSmithPaper.LTheory.Base.Complexes.CycleChainMap

/-!
# Duality map of a product

For cycles `φ ∈ M(C)_m` and `θ ∈ M(D)_n`, `(φ ⊗ θ)_♮ = (φ_♮ ⊗ θ_♮) ∘ Ξ`, where `Ξ` is the
isomorphism `(C ⊗ D)^{k-*} ≅ C^{m-*} ⊗ D^{n-*}` (`k = m + n`). The duality map `(φ ⊗ θ)_♮` needs
`φ ⊗ θ` to be a cycle, which the Leibniz rule gives; the statement takes that as the hypothesis
`hφθ` (any proof). The proof compares the two sides on each pair of summands.
-/

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Prod

namespace HSP

open DualCat

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
  have := P.hasMapBifunctor_of_finite hC hD
  have := P.hasMapBifunctor_of_finite (dualCx_finite hC m) (dualCx_finite hD n)
  ext r
  refine cxProd.hom_ext_to P hC hD fun a b hab => ?_
  refine cxProd.dual_hom_ext P hC hD fun x₁ x₂ hx => ?_
  obtain ⟨a', rfl⟩ : ∃ a', x₁ = m - a' := ⟨m - x₁, by ring⟩
  obtain ⟨b', rfl⟩ : ∃ b', x₂ = n - b' := ⟨n - x₂, by ring⟩
  have hab' : a' + b' = r := by omega
  -- the right side
  simp only [HomologicalComplex.comp_f, Category.assoc]
  rw [prodDualIso_hom_block_assoc P hC hD m n k hk hab',
    Linear.units_smul_comp, Category.assoc,
    cxProd.ι, HomologicalComplex.ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ hab',
    HomologicalComplex.ι_mapBifunctorMap_assoc,
    ← HomologicalComplex.ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ hab']
  -- the left side
  rw [StructureCx.toHom_f]
  change dualHom (cxProd.π P hC hD (m - a') (n - b') (k - r)) ≫
      strProd P hC hD φ θ k hk ⟨(r, k - r), by ring⟩ ≫ cxProd.π P hC hD a b r = _
  rw [strProd, Preadditive.sum_comp, Preadditive.comp_sum]
  by_cases hm : (a, b) ∈ cxProd.supp hC hD r
  · rw [Finset.sum_eq_single (a, b)]
    · simp only [Linear.units_smul_comp, Linear.comp_units_smul, Category.assoc,
        cxProd.ι_π_self P hC hD hab, Category.comp_id]
      by_cases he : a' = a ∧ b' = b
      · obtain ⟨h1, h2⟩ := he
        subst a' b'
        rw [← Category.assoc, ← dualHom_comp, cxProd.ι_π_self P hC hD (by omega), dualHom_id,
          Category.id_comp, cxProd.ι_π_self P hC hD hab]
        simp only [Functor.curry_obj_map_app, Functor.curry_obj_obj_map, Category.comp_id,
          StructureCx.toHom_f]
        rw [← P.tensor.map_comp_assoc, CategoryTheory.prod_comp]
        simp
      · rw [← Category.assoc, ← dualHom_comp,
          cxProd.ι_π_of_ne P hC hD (fun h' => he ⟨by omega, by omega⟩), dualHom_zero,
          zero_comp, smul_zero, cxProd.ι_π_of_ne P hC hD (fun h' => he ⟨h'.1, h'.2⟩),
          comp_zero, comp_zero, comp_zero, smul_zero]
    · rintro y _ hy
      rw [Linear.units_smul_comp, Linear.comp_units_smul, Category.assoc, Category.assoc,
        Category.assoc, cxProd.ι_π_of_ne P hC hD (fun h' => hy (Prod.ext h'.1 h'.2)),
        comp_zero, comp_zero, comp_zero, comp_zero, smul_zero]
    · exact fun h' => absurd hm h'
  · exact (cxProd.isZero_of_not_mem_supp P hC hD hab hm).eq_of_tgt _ _

end HSP
