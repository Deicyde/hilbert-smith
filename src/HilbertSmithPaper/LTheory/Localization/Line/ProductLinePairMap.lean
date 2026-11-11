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
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.ProductTotal
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.ProductHomExt
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.ProductDualHomExt
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.SummandZero
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.InclusionProjectionNe
import HilbertSmithPaper.LTheory.Base.Complexes.CycleChainMap

/-!
# The pair map of a product with the line

Let `f : C ⟶ D` carry pair data `(δφ, φ)` in `Kar C_{ℤ^j} A`, with pair map
`ψ : D^{n-*} ⟶ 𝒞(f)`. Let `J : 𝒞(f) ⊗ Λ ≅ 𝒞(f ⊗ 1)` be the isomorphism that is the canonical one
on `D_a ⊠ Λ_b` and `(-1)^b` times the canonical one on `C_{a-1} ⊠ Λ_b`. Then the pair map of
`(f ⊗ 1, δφ ⊗ λ, φ ⊗ λ)` is `J ∘ (ψ ⊗ λ_♮) ∘ Ξ`, with `Ξ` the duality isomorphism of products.

Lean: the private construction of `J` and the comparison of pair maps are carried out for any
duality pairing and any cycle `θ` in place of `λ`.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents
open scoped CategoryTheory.Prod

namespace HSP

open DualCat

section General

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {B : Type u₁} [Category.{v₁} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]
  {E : Type u₂} [Category.{v₂} E] [Preadditive E] [Linear ℚ E] [HasFiniteBiproducts E]
  [DualCat E]
  {B'' : Type u₃} [Category.{v₃} B''] [Preadditive B''] [Linear ℚ B''] [HasFiniteBiproducts B'']
  [DualCat B'']
  (P : DualityPairing B E B'')

namespace ProdLine

private lemma tmap_comp {N N' N'' : B} {V V' V'' : E} (f : N ⟶ N') (f' : N' ⟶ N'') (g : V ⟶ V')
    (g' : V' ⟶ V'') :
    P.tensor.map (f ×ₘ g) ≫ P.tensor.map (f' ×ₘ g') = P.tensor.map ((f ≫ f') ×ₘ (g ≫ g')) := by
  rw [← P.tensor.map_comp, prod_comp]

private lemma tmap_comp_assoc {N N' N'' : B} {V V' V'' : E} (f : N ⟶ N') (f' : N' ⟶ N'')
    (g : V ⟶ V') (g' : V' ⟶ V'') {Z : B''} (h : P.tensor.obj (N'', V'') ⟶ Z) :
    P.tensor.map (f ×ₘ g) ≫ P.tensor.map (f' ×ₘ g') ≫ h =
      P.tensor.map ((f ≫ f') ×ₘ (g ≫ g')) ≫ h := by
  rw [← Category.assoc, tmap_comp]

private lemma tmap_units_smul_left {N N' : B} {V V' : E} (u : ℤˣ) (f : N ⟶ N') (g : V ⟶ V') :
    P.tensor.map ((u • f) ×ₘ g) = u • P.tensor.map (f ×ₘ g) := by
  rw [Units.smul_def, Units.smul_def, ← Int.cast_smul_eq_zsmul ℚ, P.map_smul_left,
    Int.cast_smul_eq_zsmul]

private lemma tmap_zero_left {N N' : B} {V V' : E} (g : V ⟶ V') :
    P.tensor.map ((0 : N ⟶ N') ×ₘ g) = 0 := by
  simpa using P.map_smul_left 0 (0 : N ⟶ N') g

variable {C D : ChainComplex B ℤ} (f : C ⟶ D) {L : ChainComplex E ℤ}
  (hC : {r | ¬ IsZero (C.X r)}.Finite) (hD : {r | ¬ IsZero (D.X r)}.Finite)
  (hK : {r | ¬ IsZero ((cone f).X r)}.Finite) (hL : {r | ¬ IsZero (L.X r)}.Finite)

/-- The differential on a summand (a copy of the private `cxProd.ι_d`). -/
private lemma ι_d {C : ChainComplex B ℤ} (hC : {r | ¬ IsZero (C.X r)}.Finite) {p q r r' p' q' : ℤ}
    (h : p + q = r) (hp : p' + 1 = p) (hq : q' + 1 = q) :
    cxProd.ι P hC hL p q r ≫ (cxProd P C L hC hL).d r r' =
      P.tensor.map (C.d p p' ×ₘ 𝟙 (L.X q)) ≫ cxProd.ι P hC hL p' q r' +
        p.negOnePow • (P.tensor.map (𝟙 (C.X p) ×ₘ L.d q q') ≫ cxProd.ι P hC hL p q' r') := by
  have := P.hasMapBifunctor_of_finite hC hL
  have hp' : (ComplexShape.down ℤ).Rel p p' := hp
  have hq' : (ComplexShape.down ℤ).Rel q q' := hq
  rw [cxProd.ι, HomologicalComplex.ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ h,
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

/-- `ι ≫ (f ⊗ 1) = (f ⊠ 1) ≫ ι`. -/
private lemma ι_map {a b r : ℤ} (h : a + b = r) :
    cxProd.ι P hC hL a b r ≫ (cxProdMap P f (𝟙 L) hC hL hD hL).f r =
      P.tensor.map (f.f a ×ₘ 𝟙 (L.X b)) ≫ cxProd.ι P hD hL a b r := by
  have := P.hasMapBifunctor_of_finite hC hL
  have := P.hasMapBifunctor_of_finite hD hL
  rw [cxProd.ι, cxProd.ι, HomologicalComplex.ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ h,
    HomologicalComplex.ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ h,
    HomologicalComplex.ι_mapBifunctorMap]
  simp only [Functor.curry_obj_map_app, Functor.curry_obj_obj_map, HomologicalComplex.id_f]
  rw [← Category.assoc, ← P.tensor.map_comp, prod_comp, Category.comp_id, Category.id_comp]

/-- The component of `J` on `𝒞(f)_a ⊠ L_b`. -/
private noncomputable def jc (a b r : ℤ) :
    P.tensor.obj ((cone f).X a, L.X b) ⟶ (cone (cxProdMap P f (𝟙 L) hC hL hD hL)).X r :=
  P.tensor.map (biprod.fst ×ₘ 𝟙 (L.X b)) ≫ cxProd.ι P hD hL a b r ≫ biprod.inl +
    b.negOnePow • (P.tensor.map (biprod.snd ×ₘ 𝟙 (L.X b)) ≫
      cxProd.ι P hC hL (a - 1) b (r - 1) ≫ biprod.inr)

/-- `J` in degree `r`. -/
private noncomputable def jF (r : ℤ) :
    (cxProd P (cone f) L hK hL).X r ⟶ (cone (cxProdMap P f (𝟙 L) hC hL hD hL)).X r :=
  haveI := P.hasMapBifunctor_of_finite hK hL
  HomologicalComplex.mapBifunctorDesc (K₁ := cone f) (K₂ := L) (F := Functor.curry.obj P.tensor)
    (c := ComplexShape.down ℤ) (j := r) fun a b _ => jc P f hC hD hL a b r

@[reassoc]
private lemma ι_jF {a b r : ℤ} (h : a + b = r) :
    cxProd.ι P hK hL a b r ≫ jF P f hC hD hK hL r = jc P f hC hD hL a b r := by
  have := P.hasMapBifunctor_of_finite hK hL
  rw [cxProd.ι, HomologicalComplex.ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ h, jF,
    HomologicalComplex.ι_mapBifunctorDesc]

private lemma sign_aux (a b : ℤ) :
    b.negOnePow * (a + b - 1).negOnePow = (a - 1).negOnePow := by
  rw [show a + b - 1 = (a - 1) + b by ring, Int.negOnePow_add, mul_comm, mul_assoc,
    Int.units_mul_self, mul_one]

private lemma sign_aux2 (a b : ℤ) :
    b.negOnePow * (a - 1).negOnePow = a.negOnePow * (b - 1).negOnePow := by
  rw [Int.negOnePow_sub, Int.negOnePow_sub, Int.negOnePow_one]
  exact mul_left_comm _ _ _

private lemma jF_comm (i j : ℤ) (hij : (ComplexShape.down ℤ).Rel i j) :
    jF P f hC hD hK hL i ≫ (cone (cxProdMap P f (𝟙 L) hC hL hD hL)).d i j =
      (cxProd P (cone f) L hK hL).d i j ≫ jF P f hC hD hK hL j := by
  have := P.hasMapBifunctor_of_finite hK hL
  simp only [ComplexShape.down_Rel] at hij
  obtain rfl : j = i - 1 := by omega
  refine HomologicalComplex.mapBifunctor.hom_ext fun a b hab => ?_
  change a + b = i at hab
  rw [← HomologicalComplex.ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ hab]
  change cxProd.ι P hK hL a b i ≫ _ = cxProd.ι P hK hL a b i ≫ _
  rw [ι_jF_assoc P f hC hD hK hL hab,
    ← Category.assoc, ι_d P hL hK hab (sub_add_cancel a 1) (sub_add_cancel b 1)]
  simp only [Preadditive.add_comp, Linear.units_smul_comp, Category.assoc,
    ι_jF P f hC hD hK hL (show a - 1 + b = i - 1 by omega),
    ι_jF P f hC hD hK hL (show a + (b - 1) = i - 1 by omega)]
  change jc P f hC hD hL a b i ≫ cone.d _ i (i - 1) = _
  simp only [jc, cone.d, dite_true, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.comp_id]
  subst hab
  apply biprod.hom_ext
  · simp only [Preadditive.add_comp, Linear.units_smul_comp, Category.assoc, biprod.lift_fst,
      biprod.inl_fst_assoc, biprod.inr_fst_assoc, Preadditive.comp_add, Linear.comp_units_smul,
      zero_comp, smul_zero, add_zero, zero_add, biprod.inl_snd_assoc,
      biprod.inr_snd_assoc]
    rw [ι_d P hL hD rfl (sub_add_cancel a 1) (sub_add_cancel b 1),
      ι_map P f hC hD hL (show a - 1 + b = a + b - 1 by omega)]
    simp only [tmap_comp_assoc, Preadditive.comp_add, Linear.comp_units_smul, biprod.lift_fst,
      Category.id_comp, Category.comp_id, P.map_add_left, tmap_units_smul_left,
      Preadditive.add_comp,
      Linear.units_smul_comp, smul_smul, sign_aux, biprod.inl_fst, biprod.inr_fst,
      biprod.lift_fst, 
      comp_zero, smul_zero, add_zero]
    abel
  · simp only [Preadditive.add_comp, Linear.units_smul_comp, Category.assoc, biprod.lift_snd,
      biprod.inl_snd_assoc, biprod.inr_snd_assoc, Preadditive.comp_add, Linear.comp_units_smul,
      comp_zero, zero_comp, zero_add]
    rw [ι_d P hL hC (show a - 1 + b = a + b - 1 by omega) (sub_add_cancel (a - 1) 1)
      (sub_add_cancel b 1)]
    simp only [tmap_comp_assoc, Preadditive.comp_add, Linear.comp_units_smul, biprod.lift_snd,
      Category.id_comp, Category.comp_id, 
      smul_smul, smul_add, 
      biprod.inl_snd, biprod.inr_snd, biprod.lift_snd, 
      comp_zero, zero_add, sign_aux2]

/-- The inverse of `J` in degree `r`. -/
private noncomputable def jinvF (r : ℤ) :
    (cone (cxProdMap P f (𝟙 L) hC hL hD hL)).X r ⟶ (cxProd P (cone f) L hK hL).X r :=
  ∑ x ∈ cxProd.supp hK hL r,
    (biprod.fst ≫ cxProd.π P hD hL x.1 x.2 r ≫
        P.tensor.map ((biprod.inl : D.X x.1 ⟶ (cone f).X x.1) ×ₘ 𝟙 (L.X x.2)) +
      x.2.negOnePow • (biprod.snd ≫ cxProd.π P hC hL (x.1 - 1) x.2 (r - 1) ≫
        P.tensor.map ((biprod.inr : C.X (x.1 - 1) ⟶ (cone f).X x.1) ×ₘ 𝟙 (L.X x.2)))) ≫
      cxProd.ι P hK hL x.1 x.2 r

omit [Linear ℚ B] [DualCat B] [Linear ℚ E] [HasFiniteBiproducts E] [DualCat E] in
private lemma mem_supp_D {a b r : ℤ} (h : a + b = r) (hm : (a, b) ∉ cxProd.supp hK hL r) :
    (a, b) ∉ cxProd.supp hD hL r := by
  rw [cxProd.mem_supp] at hm ⊢
  rintro ⟨⟨h1, h2⟩, -⟩
  exact hm ⟨⟨fun h' => h1 ((biprod_isZero_iff _ _).1 h').1, h2⟩, h⟩

omit [Linear ℚ B] [DualCat B] [Linear ℚ E] [HasFiniteBiproducts E] [DualCat E] in
private lemma mem_supp_C {a b r : ℤ} (h : a + b = r) (hm : (a, b) ∉ cxProd.supp hK hL r) :
    (a - 1, b) ∉ cxProd.supp hC hL (r - 1) := by
  rw [cxProd.mem_supp] at hm ⊢
  rintro ⟨⟨h1, h2⟩, -⟩
  exact hm ⟨⟨fun h' => h1 ((biprod_isZero_iff _ _).1 h').2, h2⟩, h⟩

@[reassoc]
private lemma inl_jinvF {a b r : ℤ} (h : a + b = r) :
    cxProd.ι P hD hL a b r ≫ biprod.inl ≫ jinvF P f hC hD hK hL r =
      P.tensor.map ((biprod.inl : D.X a ⟶ (cone f).X a) ×ₘ 𝟙 (L.X b)) ≫
        cxProd.ι P hK hL a b r := by
  by_cases hm : (a, b) ∈ cxProd.supp hK hL r
  · rw [jinvF, Preadditive.comp_sum, Preadditive.comp_sum, Finset.sum_eq_single (a, b)]
    · simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc, biprod.inl_fst_assoc,
        biprod.inl_snd_assoc, zero_comp, Linear.units_smul_comp, Linear.comp_units_smul,
        smul_zero, add_zero, cxProd.ι_π_self_assoc P hD hL h]
    · rintro x - hx
      simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc, biprod.inl_fst_assoc,
        biprod.inl_snd_assoc, zero_comp, Linear.units_smul_comp, Linear.comp_units_smul,
        smul_zero, add_zero,
        cxProd.ι_π_of_ne_assoc P hD hL (fun h' => hx (Prod.ext h'.1 h'.2).symm)]
    · exact fun h' => absurd hm h'
  · exact (cxProd.isZero_of_not_mem_supp P hD hL h (mem_supp_D f hD hK hL h hm)).eq_of_src _ _

@[reassoc]
private lemma inr_jinvF {a b r : ℤ} (h : a + b = r) :
    cxProd.ι P hC hL (a - 1) b (r - 1) ≫ biprod.inr ≫ jinvF P f hC hD hK hL r =
      b.negOnePow • (P.tensor.map ((biprod.inr : C.X (a - 1) ⟶ (cone f).X a) ×ₘ 𝟙 (L.X b)) ≫
        cxProd.ι P hK hL a b r) := by
  by_cases hm : (a, b) ∈ cxProd.supp hK hL r
  · rw [jinvF, Preadditive.comp_sum, Preadditive.comp_sum, Finset.sum_eq_single (a, b)]
    · simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc, biprod.inr_fst_assoc,
        biprod.inr_snd_assoc, zero_comp, Linear.units_smul_comp, Linear.comp_units_smul,
        zero_add, cxProd.ι_π_self_assoc P hC hL (show a - 1 + b = r - 1 by omega)]
    · rintro x - hx
      simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc, biprod.inr_fst_assoc,
        biprod.inr_snd_assoc, zero_comp, Linear.units_smul_comp, Linear.comp_units_smul,
        smul_zero, zero_add, cxProd.ι_π_of_ne_assoc P hC hL (p := a - 1) (q := b) (p' := x.1 - 1)
          (q' := x.2) (r := r - 1) (fun h' => hx (Prod.ext (show x.1 = a by have := h'.1; omega)
            (show x.2 = b from h'.2.symm)))]
    · exact fun h' => absurd hm h'
  · exact (cxProd.isZero_of_not_mem_supp P hC hL (by omega)
      (mem_supp_C f hC hK hL h hm)).eq_of_src _ _

private lemma jF_jinvF (r : ℤ) : jF P f hC hD hK hL r ≫ jinvF P f hC hD hK hL r = 𝟙 _ := by
  have := P.hasMapBifunctor_of_finite hK hL
  refine HomologicalComplex.mapBifunctor.hom_ext fun a b hab => ?_
  change a + b = r at hab
  rw [← HomologicalComplex.ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ hab]
  change cxProd.ι P hK hL a b r ≫ _ = cxProd.ι P hK hL a b r ≫ _
  rw [ι_jF_assoc P f hC hD hK hL hab, jc]
  simp only [Preadditive.add_comp, Linear.units_smul_comp, Category.assoc,
    inl_jinvF P f hC hD hK hL hab, inr_jinvF P f hC hD hK hL hab, Linear.comp_units_smul, smul_smul,
    Int.units_mul_self, one_smul, tmap_comp_assoc, Category.comp_id]
  rw [← Preadditive.add_comp, ← P.map_add_left, biprod.total, ← prod_id, P.tensor.map_id,
    Category.id_comp]

private lemma jinvF_jF (r : ℤ) : jinvF P f hC hD hK hL r ≫ jF P f hC hD hK hL r = 𝟙 _ := by
  have := P.hasMapBifunctor_of_finite hC hL
  have := P.hasMapBifunctor_of_finite hD hL
  apply biprod.hom_ext'
  · refine HomologicalComplex.mapBifunctor.hom_ext fun a b hab => ?_
    change a + b = r at hab
    rw [← HomologicalComplex.ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ hab]
    change cxProd.ι P hD hL a b r ≫ _ = cxProd.ι P hD hL a b r ≫ _
    rw [inl_jinvF_assoc P f hC hD hK hL hab, ι_jF P f hC hD hK hL hab, jc]
    simp only [Preadditive.comp_add, Linear.comp_units_smul, tmap_comp_assoc, biprod.inl_fst,
      biprod.inl_snd, tmap_zero_left, zero_comp, smul_zero, add_zero, Category.comp_id]
    rw [← prod_id, P.tensor.map_id, Category.id_comp]
  · refine HomologicalComplex.mapBifunctor.hom_ext fun p b hpb => ?_
    change p + b = r - 1 at hpb
    obtain ⟨a, rfl⟩ : ∃ a, p = a - 1 := ⟨p + 1, by ring⟩
    have hab : a + b = r := by omega
    rw [← HomologicalComplex.ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ hpb]
    change cxProd.ι P hC hL (a - 1) b (r - 1) ≫ _ = cxProd.ι P hC hL (a - 1) b (r - 1) ≫ _
    rw [inr_jinvF_assoc P f hC hD hK hL hab, Linear.units_smul_comp, Category.assoc,
      ι_jF P f hC hD hK hL hab, jc]
    simp only [Preadditive.comp_add, Linear.comp_units_smul, tmap_comp_assoc, biprod.inr_fst,
      biprod.inr_snd, tmap_zero_left, zero_comp, zero_add, Category.comp_id, smul_smul,
      Int.units_mul_self, one_smul]
    rw [← prod_id, P.tensor.map_id, Category.id_comp]

/-- The isomorphism `J : 𝒞(f) ⊗ L ≅ 𝒞(f ⊗ 1)`. -/
private noncomputable def jIso :
    cxProd P (cone f) L hK hL ≅ cone (cxProdMap P f (𝟙 L) hC hL hD hL) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun r => ⟨jF P f hC hD hK hL r, jinvF P f hC hD hK hL r, jF_jinvF P f hC hD hK hL r,
      jinvF_jF P f hC hD hK hL r⟩) (jF_comm P f hC hD hK hL)

private lemma map_π {c d s : ℤ} :
    (cxProdMap P f (𝟙 L) hC hL hD hL).f s ≫ cxProd.π P hD hL c d s =
      cxProd.π P hC hL c d s ≫ P.tensor.map (f.f c ×ₘ 𝟙 (L.X d)) := by
  have := P.hasMapBifunctor_of_finite hC hL
  refine HomologicalComplex.mapBifunctor.hom_ext fun p q hpq => ?_
  change p + q = s at hpq
  rw [← HomologicalComplex.ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ hpq]
  change cxProd.ι P hC hL p q s ≫ _ = cxProd.ι P hC hL p q s ≫ _
  rw [← Category.assoc, ι_map P f hC hD hL hpq]
  by_cases he : p = c ∧ q = d
  · obtain ⟨rfl, rfl⟩ := he
    rw [Category.assoc, cxProd.ι_π_self P hD hL hpq, cxProd.ι_π_self_assoc P hC hL hpq,
      Category.comp_id]
  · rw [Category.assoc, cxProd.ι_π_of_ne P hD hL he, cxProd.ι_π_of_ne_assoc P hC hL he, comp_zero,
      zero_comp]

private lemma sign_snd (a b n m : ℤ) (hmn : m + 1 = n) :
    (a + b).negOnePow * (b * (a - 1 + m)).negOnePow =
      (b * (a + n)).negOnePow * (b.negOnePow * a.negOnePow) := by
  rw [← Int.negOnePow_add, ← Int.negOnePow_add, ← Int.negOnePow_add, Int.negOnePow_eq_iff]
  exact ⟨-b, by subst hmn; ring⟩

@[reassoc]
private lemma pairMap_fst {C' D' : ChainComplex B ℤ} (g : C' ⟶ D') {m n : ℤ} (hmn : m + 1 = n)
    (δφ : (StructureCx D').X n) (φ : (StructureCx C').X m)
    (hφ : (StructureCx C').d m (m - 1) φ = 0)
    (hδφ : (StructureCx D').d n m δφ = (StructureCx.push g).f m φ) (r : ℤ) :
    (pairMap g hmn δφ φ hφ hδφ).f r ≫ biprod.fst = δφ ⟨(r, n - r), by ring⟩ :=
  biprod.lift_fst _ _

@[reassoc]
private lemma pairMap_snd {B' : Type*} [Category B'] [Preadditive B'] [Linear ℚ B']
    [HasFiniteBiproducts B'] [DualCat B'] {C' D' : ChainComplex B' ℤ} (g : C' ⟶ D') {m n : ℤ}
    (hmn : m + 1 = n) (δφ : (StructureCx D').X n) (φ : (StructureCx C').X m)
    (hφ : (StructureCx C').d m (m - 1) φ = 0)
    (hδφ : (StructureCx D').d n m δφ = (StructureCx.push g).f m φ) (r : ℤ) :
    (pairMap g hmn δφ φ hφ hδφ).f r ≫ biprod.snd =
      r.negOnePow • (dualHom (g.f (n - r)) ≫ φ ⟨(r - 1, n - r), by omega⟩) :=
  biprod.lift_snd _ _

private theorem pairMap_eq {m n : ℤ} (hmn : m + 1 = n) (δφ : (StructureCx D).X n)
    (φ : (StructureCx C).X m) (hφ : (StructureCx C).d m (m - 1) φ = 0)
    (hδφ : (StructureCx D).d n m δφ = (StructureCx.push f).f m φ) {l : ℤ}
    (θ : (StructureCx L).X l) (hθ : (StructureCx L).d l (l - 1) θ = 0)
    (hφ' : (StructureCx (cxProd P C L hC hL)).d (m + l) (m + l - 1)
      (strProd P hC hL φ θ (m + l) rfl) = 0)
    (hδφ' : (StructureCx (cxProd P D L hD hL)).d (n + l) (m + l)
      (strProd P hD hL δφ θ (n + l) rfl) =
      (StructureCx.push (cxProdMap P f (𝟙 L) hC hL hD hL)).f (m + l)
        (strProd P hC hL φ θ (m + l) rfl)) :
    pairMap (cxProdMap P f (𝟙 L) hC hL hD hL) (show m + l + 1 = n + l by omega)
        (strProd P hD hL δφ θ (n + l) rfl) (strProd P hC hL φ θ (m + l) rfl) hφ' hδφ' =
      (prodDualIso P hD hL n l (n + l) rfl).hom ≫
        cxProdMap P (pairMap f hmn δφ φ hφ hδφ) (StructureCx.toHom θ hθ)
          (dualCx_finite hD n) (dualCx_finite hL l) hK hL ≫ (jIso P f hC hD hK hL).hom := by
  have := P.hasMapBifunctor_of_finite (dualCx_finite hD n) (dualCx_finite hL l)
  have := P.hasMapBifunctor_of_finite hK hL
  refine HomologicalComplex.hom_ext _ _ fun r => ?_
  apply biprod.hom_ext
  · refine cxProd.hom_ext_to P hD hL fun a b hab => ?_
    refine cxProd.dual_hom_ext P hD hL fun x₁ x₂ hx => ?_
    obtain ⟨a', rfl⟩ : ∃ a', x₁ = n - a' := ⟨n - x₁, by ring⟩
    obtain ⟨b', rfl⟩ : ∃ b', x₂ = l - b' := ⟨l - x₂, by ring⟩
    have hab' : a' + b' = r := by omega
    simp only [HomologicalComplex.comp_f, Category.assoc]
    rw [prodDualIso_hom_block_assoc P hD hL n l (n + l) rfl hab', Linear.units_smul_comp,
      Category.assoc, cxProd.ι, HomologicalComplex.ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ hab',
      HomologicalComplex.ι_mapBifunctorMap_assoc,
      ← HomologicalComplex.ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ hab']
    change _ = _ • (_ ≫ _ ≫ _ ≫ cxProd.ι P hK hL a' b' r ≫ jF P f hC hD hK hL r ≫ _)
    rw [ι_jF_assoc P f hC hD hK hL hab', jc]
    change dualHom (cxProd.π P hD hL (n - a') (l - b') (n + l - r)) ≫
      biprod.lift (strProd P hD hL δφ θ (n + l) rfl ⟨(r, n + l - r), by ring⟩) _ ≫ _ ≫ _ = _
    rw [biprod.lift_fst_assoc]
    by_cases he : a = a' ∧ b = b'
    · obtain ⟨rfl, rfl⟩ := he
      rw [strProd_block P hD hL δφ θ (n + l) rfl (by ring) hab (by ring) (by ring)]
      simp only [Preadditive.add_comp, Category.assoc, biprod.inl_fst_assoc, biprod.inr_fst_assoc,
        Linear.units_smul_comp, zero_comp, comp_zero, smul_zero, add_zero,
        cxProd.ι_π_self P hD hL hab, Category.comp_id, Functor.curry_obj_map_app,
        Functor.curry_obj_obj_map, tmap_comp, Category.id_comp,
        pairMap_fst f, StructureCx.toHom_f]
    · rw [strProd_block_of_ne P hD hL δφ θ (n + l) rfl (by ring)
        (fun h' => he ⟨by omega, by omega⟩)]
      simp only [Preadditive.add_comp, Category.assoc, biprod.inl_fst_assoc, biprod.inr_fst_assoc,
        Linear.units_smul_comp, zero_comp, comp_zero, smul_zero, add_zero,
        cxProd.ι_π_of_ne P hD hL (p := a') (q := b') (p' := a) (q' := b) (r := r)
          (fun h' => he ⟨h'.1.symm, h'.2.symm⟩)]
  · refine cxProd.hom_ext_to P hC hL fun a b hab => ?_
    refine cxProd.dual_hom_ext P hD hL fun x₁ x₂ hx => ?_
    obtain ⟨a', rfl⟩ : ∃ a', x₁ = n - a' := ⟨n - x₁, by ring⟩
    obtain ⟨b', rfl⟩ : ∃ b', x₂ = l - b' := ⟨l - x₂, by ring⟩
    have hab' : a' + b' = r := by omega
    simp only [HomologicalComplex.comp_f, Category.assoc]
    rw [prodDualIso_hom_block_assoc P hD hL n l (n + l) rfl hab', Linear.units_smul_comp,
      Category.assoc, cxProd.ι, HomologicalComplex.ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ hab',
      HomologicalComplex.ι_mapBifunctorMap_assoc,
      ← HomologicalComplex.ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ hab']
    change _ = _ • (_ ≫ _ ≫ _ ≫ cxProd.ι P hK hL a' b' r ≫ jF P f hC hD hK hL r ≫ _)
    rw [ι_jF_assoc P f hC hD hK hL hab', jc, pairMap_snd_assoc, Linear.units_smul_comp,
      Linear.comp_units_smul, Category.assoc, ← Category.assoc (dualHom _) (dualHom _),
      ← dualHom_comp,
      map_π P f hC hD hL, dualHom_comp, Category.assoc]
    by_cases he : a = a' - 1 ∧ b = b'
    · obtain ⟨rfl, rfl⟩ := he
      rw [strProd_block P hC hL φ θ (m + l) rfl (by omega) hab (by omega) (by ring)]
      simp only [Preadditive.add_comp, Category.assoc, biprod.inl_snd_assoc, biprod.inr_snd_assoc,
        Linear.units_smul_comp, zero_comp, comp_zero, zero_add,
        cxProd.ι_π_self P hC hL hab, Category.comp_id, Functor.curry_obj_map_app,
        Functor.curry_obj_obj_map, tmap_comp, Category.id_comp,
        pairMap_snd f, StructureCx.toHom_f, Linear.comp_units_smul, tmap_units_smul_left, smul_smul]
      rw [← Category.assoc, P.κ_natural, dualHom_id, Category.assoc, tmap_comp, Category.id_comp,
        ← hab', sign_snd a' b n m hmn]
    · rw [strProd_block_of_ne P hC hL φ θ (m + l) rfl (by omega)
        (fun h' => he ⟨by omega, by omega⟩)]
      simp only [Preadditive.add_comp, Category.assoc, biprod.inl_snd_assoc, biprod.inr_snd_assoc,
        Linear.units_smul_comp, zero_comp, comp_zero, smul_zero, zero_add,
        cxProd.ι_π_of_ne P hC hL (p := a' - 1) (q := b') (p' := a) (q' := b) (r := r - 1)
          (fun h' => he ⟨h'.1.symm, h'.2.symm⟩)]

end ProdLine

end General

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
            (dualCx_finite hD n) (dualCx_finite hΛ 1) hK hΛ ≫ J.hom :=
  ⟨ProdLine.jIso _ f hC hD hK hΛ, fun _ _ _ h => ProdLine.ι_jF _ f hC hD hK hΛ h,
    ProdLine.pairMap_eq _ f hC hD hK hΛ hmn δφ φ hφ hδφ symLine.str symLine.str_T_and_cycle.2 hφ'
      hδφ'⟩

end HSP
