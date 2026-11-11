import Mathlib
import HilbertSmithPaper.LTheory.Base.Complexes.SumOfComplexes
import HilbertSmithPaper.LTheory.Localization.Products.ProductPush
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.ProductMapComp
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.ProductMapId
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.ProductAdditiveLeft

/-!
# Products distribute over sums

For a duality pairing `(⊠, κ)`, complexes `C`, `C'`, `D` with finitely many nonzero chain objects,
`φ ∈ M(C)_m`, `φ' ∈ M(C')_m` and `θ ∈ M(D)_n`, the canonical isomorphism
`(C ⊕ C') ⊗ D ≅ C ⊗ D ⊕ C' ⊗ D`, with components `p ⊗ 1` for the projections `p` of `C ⊕ C'`,
carries `(φ ⊕ φ') ⊗ θ` to `φ ⊗ θ ⊕ φ' ⊗ θ`. Its inverse has components `i ⊗ 1` for the inclusions,
and the pushforward of `φ ⊗ θ` along `i ⊗ 1` is `i_% φ ⊗ θ` (`HSP.strProd_push`).
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

private lemma push_push {C D D' : ChainComplex B ℤ} (g : C ⟶ D) (h : D ⟶ D') (n : ℤ)
    (x : (StructureCx C).X n) :
    (StructureCx.push h).f n ((StructureCx.push g).f n x) = (StructureCx.push (g ≫ h)).f n x := by
  rw [StructureCx.push_comp]
  rfl

private lemma push_id_apply (C : ChainComplex B ℤ) (n : ℤ) (x : (StructureCx C).X n) :
    (StructureCx.push (𝟙 C)).f n x = x := by
  rw [StructureCx.push_id]
  rfl

private lemma cxProdMap_add_left (P : DualityPairing B E B'') {C C' : ChainComplex B ℤ}
    {D D' : ChainComplex E ℤ} (f f' : C ⟶ C') (g : D ⟶ D')
    (hC : {r | ¬ IsZero (C.X r)}.Finite) (hD : {r | ¬ IsZero (D.X r)}.Finite)
    (hC' : {r | ¬ IsZero (C'.X r)}.Finite) (hD' : {r | ¬ IsZero (D'.X r)}.Finite) :
    cxProdMap P (f + f') g hC hD hC' hD' =
      cxProdMap P f g hC hD hC' hD' + cxProdMap P f' g hC hD hC' hD' := by
  have := P.hasMapBifunctor_of_finite hC hD
  have := P.hasMapBifunctor_of_finite hC' hD'
  ext j p q h
  simp only [HomologicalComplex.add_f_apply, Preadditive.comp_add,
    HomologicalComplex.ι_mapBifunctorMap, Functor.curry_obj_map_app, Functor.curry_obj_obj_map,
    ← Functor.map_comp_assoc, CategoryTheory.prod_comp, Category.id_comp, Category.comp_id,
    P.map_add_left, Preadditive.add_comp]

private lemma cxProdMap_zero_left (P : DualityPairing B E B'') {C C' : ChainComplex B ℤ}
    {D D' : ChainComplex E ℤ} (g : D ⟶ D')
    (hC : {r | ¬ IsZero (C.X r)}.Finite) (hD : {r | ¬ IsZero (D.X r)}.Finite)
    (hC' : {r | ¬ IsZero (C'.X r)}.Finite) (hD' : {r | ¬ IsZero (D'.X r)}.Finite) :
    cxProdMap P (0 : C ⟶ C') g hC hD hC' hD' = 0 := by
  have h := cxProdMap_add_left P (0 : C ⟶ C') 0 g hC hD hC' hD'
  rw [add_zero] at h
  simpa using h.symm

/-- The canonical isomorphism `C ⊗ D ⊕ C' ⊗ D ≅ (C ⊕ C') ⊗ D`. -/
private noncomputable def sumIso (P : DualityPairing B E B'') {C C' : ChainComplex B ℤ}
    {D : ChainComplex E ℤ} (hC : {r | ¬ IsZero (C.X r)}.Finite)
    (hC' : {r | ¬ IsZero (C'.X r)}.Finite) (hCC' : {r | ¬ IsZero ((C ⊞ C').X r)}.Finite)
    (hD : {r | ¬ IsZero (D.X r)}.Finite) :
    cxProd P C D hC hD ⊞ cxProd P C' D hC' hD ≅ cxProd P (C ⊞ C') D hCC' hD where
  hom := biprod.desc (cxProdMap P biprod.inl (𝟙 D) hC hD hCC' hD)
    (cxProdMap P biprod.inr (𝟙 D) hC' hD hCC' hD)
  inv := biprod.lift (cxProdMap P biprod.fst (𝟙 D) hCC' hD hC hD)
    (cxProdMap P biprod.snd (𝟙 D) hCC' hD hC' hD)
  hom_inv_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
      simp only [biprod.inl_desc_assoc, biprod.inr_desc_assoc, Category.assoc, biprod.lift_fst,
        biprod.lift_snd, ← cxProdMap_comp, biprod.inl_fst, biprod.inl_snd, biprod.inr_fst,
        biprod.inr_snd, Category.comp_id, cxProdMap_id, cxProdMap_zero_left]
  inv_hom_id := by
    rw [biprod.lift_desc, ← cxProdMap_comp, ← cxProdMap_comp, ← cxProdMap_add_left, biprod.total,
      Category.id_comp, cxProdMap_id]

/-- The isomorphism `C ⊗ D ⊕ C' ⊗ D ≅ (C ⊕ C') ⊗ D` carries `φ ⊗ θ ⊕ φ' ⊗ θ` to
`(φ ⊕ φ') ⊗ θ`. -/
private lemma push_sumIso (P : DualityPairing B E B'') {C C' : ChainComplex B ℤ}
    {D : ChainComplex E ℤ} (hC : {r | ¬ IsZero (C.X r)}.Finite)
    (hC' : {r | ¬ IsZero (C'.X r)}.Finite) (hCC' : {r | ¬ IsZero ((C ⊞ C').X r)}.Finite)
    (hD : {r | ¬ IsZero (D.X r)}.Finite) {m n : ℤ} (φ : (StructureCx C).X m)
    (φ' : (StructureCx C').X m) (θ : (StructureCx D).X n) (k : ℤ) (hk : m + n = k) :
    (StructureCx.push (sumIso P hC hC' hCC' hD).hom).f k
        (StructureCx.sum (strProd P hC hD φ θ k hk) (strProd P hC' hD φ' θ k hk)) =
      strProd P hCC' hD (StructureCx.sum φ φ') θ k hk := by
  rw [StructureCx.sum, StructureCx.sum, map_add, push_push, push_push, strProd_add_left]
  simp only [sumIso, biprod.inl_desc, biprod.inr_desc]
  rw [strProd_push, strProd_push, push_id_apply]

/-- **Products distribute over sums.** An isomorphism `(C ⊕ C') ⊗ D ≅ C ⊗ D ⊕ C' ⊗ D` carries
`(φ ⊕ φ') ⊗ θ` to `φ ⊗ θ ⊕ φ' ⊗ θ`. -/
theorem cxProd_sum_iso (P : DualityPairing B E B'') {C C' : ChainComplex B ℤ}
    {D : ChainComplex E ℤ} (hC : {r | ¬ IsZero (C.X r)}.Finite)
    (hC' : {r | ¬ IsZero (C'.X r)}.Finite) (hCC' : {r | ¬ IsZero ((C ⊞ C').X r)}.Finite)
    (hD : {r | ¬ IsZero (D.X r)}.Finite) {m n : ℤ} (φ : (StructureCx C).X m)
    (φ' : (StructureCx C').X m) (θ : (StructureCx D).X n) (k : ℤ) (hk : m + n = k) :
    ∃ u : cxProd P (C ⊞ C') D hCC' hD ≅ cxProd P C D hC hD ⊞ cxProd P C' D hC' hD,
      (StructureCx.push u.hom).f k (strProd P hCC' hD (StructureCx.sum φ φ') θ k hk) =
        StructureCx.sum (strProd P hC hD φ θ k hk) (strProd P hC' hD φ' θ k hk) := by
  refine ⟨(sumIso P hC hC' hCC' hD).symm, ?_⟩
  rw [← push_sumIso P hC hC' hCC' hD φ φ' θ k hk, Iso.symm_hom, push_push, Iso.hom_inv_id,
    push_id_apply]

end HSP
