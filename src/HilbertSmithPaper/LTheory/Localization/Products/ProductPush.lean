import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.ExternalProduct
import HilbertSmithPaper.LTheory.Base.Complexes.StructurePush

/-!
# Pushforward of products

For chain maps `f : C ⟶ C'` and `g : D ⟶ D'`, `(f ⊗ g)_% (φ ⊗ θ) = f_% φ ⊗ g_% θ`. The map
`f ⊗ g` is block diagonal with blocks `f_p ⊠ g_q`, so on each block both sides are
`(-1)^{q(p+m)} (f φ_p f^*) ⊠ (g θ_q g^*)`, by functoriality of `⊠` and naturality of `κ`.
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

/-- `f ⊗ g` followed by the projection onto `C'_a ⊠ D'_b` is the projection onto `C_a ⊠ D_b`
followed by `f_a ⊠ g_b`. -/
@[reassoc]
private lemma cxProdMap_π (P : DualityPairing B E B'') {C C' : ChainComplex B ℤ}
    {D D' : ChainComplex E ℤ} (f : C ⟶ C') (g : D ⟶ D') (hC : {r | ¬ IsZero (C.X r)}.Finite)
    (hD : {r | ¬ IsZero (D.X r)}.Finite) (hC' : {r | ¬ IsZero (C'.X r)}.Finite)
    (hD' : {r | ¬ IsZero (D'.X r)}.Finite) (a b r : ℤ) :
    (cxProdMap P f g hC hD hC' hD').f r ≫ cxProd.π P hC' hD' a b r =
      cxProd.π P hC hD a b r ≫ P.tensor.map (f.f a ×ₘ g.f b) := by
  have := P.hasMapBifunctor_of_finite hC hD
  have := P.hasMapBifunctor_of_finite hC' hD'
  ext p q h
  change p + q = r at h
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc,
    ← HomologicalComplex.ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ h,
    ← HomologicalComplex.ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ h]
  change _ ≫ _ ≫ cxProd.ι P hC' hD' p q r ≫ cxProd.π P hC' hD' a b r =
    cxProd.ι P hC hD p q r ≫ cxProd.π P hC hD a b r ≫ _
  by_cases he : p = a ∧ q = b
  · obtain ⟨rfl, rfl⟩ := he
    rw [cxProd.ι_π_self P hC' hD' h, cxProd.ι_π_self_assoc P hC hD h]
    simp only [Functor.curry_obj_map_app, Functor.curry_obj_obj_map, Category.comp_id,
      ← Functor.map_comp, CategoryTheory.prod_comp, Category.id_comp, Category.comp_id]
  · rw [cxProd.ι_π_of_ne P hC' hD' he, cxProd.ι_π_of_ne_assoc P hC hD he, comp_zero, comp_zero,
      zero_comp]

/-- **Pushforward of products.** `(f ⊗ g)_% (φ ⊗ θ) = f_% φ ⊗ g_% θ`. -/
theorem strProd_push (P : DualityPairing B E B'') {C C' : ChainComplex B ℤ}
    {D D' : ChainComplex E ℤ} (f : C ⟶ C') (g : D ⟶ D') (hC : {r | ¬ IsZero (C.X r)}.Finite)
    (hD : {r | ¬ IsZero (D.X r)}.Finite) (hC' : {r | ¬ IsZero (C'.X r)}.Finite)
    (hD' : {r | ¬ IsZero (D'.X r)}.Finite) {m n : ℤ} (φ : (StructureCx C).X m)
    (θ : (StructureCx D).X n) (k : ℤ) (hk : m + n = k) :
    (StructureCx.push (cxProdMap P f g hC hD hC' hD')).f k (strProd P hC hD φ θ k hk) =
      strProd P hC' hD' ((StructureCx.push f).f m φ) ((StructureCx.push g).f n θ) k hk := by
  funext ⟨⟨r, s⟩, hrs⟩
  rw [StructureCx.push_apply]
  refine cxProd.hom_ext_to P hC' hD' fun a b hab => ?_
  refine cxProd.dual_hom_ext P hC' hD' fun c d hcd => ?_
  simp only [Category.assoc]
  rw [cxProdMap_π, ← Category.assoc (dualHom (cxProd.π P hC' hD' c d s)), ← dualHom_comp,
    cxProdMap_π, dualHom_comp, Category.assoc]
  by_cases he : a + c = m ∧ b + d = n
  · obtain ⟨ha, hb⟩ := he
    rw [reassoc_of% (strProd_block P hC hD φ θ k hk hrs hab ha hb),
      strProd_block P hC' hD' _ _ k hk hrs hab ha hb, Linear.units_smul_comp,
      Linear.comp_units_smul, Category.assoc, reassoc_of% (P.κ_natural (f.f c) (g.f d))]
    congr 2
    rw [StructureCx.push_apply, StructureCx.push_apply, ← Functor.map_comp, ← Functor.map_comp]
    rfl
  · rw [reassoc_of% (strProd_block_of_ne P hC hD φ θ k hk hrs he),
      strProd_block_of_ne P hC' hD' _ _ k hk hrs he, zero_comp, comp_zero]

end HSP
