import Mathlib
import HilbertSmithPaper.LTheory.Base.Groups.LGroupAdd
import HilbertSmithPaper.LTheory.Base.Groups.HomotopyIsometryInvariance
import HilbertSmithPaper.LTheory.Base.Pairs.PairTransport
import HilbertSmithPaper.LTheory.Localization.Products.ProductWithLine
import HilbertSmithPaper.LTheory.Localization.Products.ProductPush
import HilbertSmithPaper.LTheory.Localization.Transitions.TransitionComplex

/-!
# Transition map

For `j ≥ 0` and `m ∈ ℤ`, the transition map
`t : L^p_m(C_{ℤ^j} A) → L^p_{m+1}(C_{ℤ^{j+1}} A)`, `[C, φ] ↦ [C ⊗ Λ, φ ⊗ λ]`, a homomorphism.

Lean: the target degree is a parameter `m'` with `m + 1 = m'`, so that the lower-L-group version
needs no transport along `k + j + 1 = k + (j + 1)`. Products are taken for the box product pairing
`HSP.boxPairingPow A j`. The finiteness of the nonzero chain objects, needed to form the products,
follows from boundedness.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents
open scoped CategoryTheory.Prod

namespace HSP

open DualCat

universe v u

section General

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {B : Type u₁} [Category.{v₁} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]
  {E : Type u₂} [Category.{v₂} E] [Preadditive E] [Linear ℚ E] [HasFiniteBiproducts E]
  [DualCat E]
  {B'' : Type u₃} [Category.{v₃} B''] [Preadditive B''] [Linear ℚ B''] [HasFiniteBiproducts B'']
  [DualCat B'']

omit [Linear ℚ B] [HasFiniteBiproducts B] [DualCat B] in
/-- A complex whose chain objects vanish outside `[0, k]` has finitely many nonzero ones. -/
private lemma finite_of_bounded {C : ChainComplex B ℤ} {k : ℤ}
    (h : ∀ r : ℤ, r < 0 ∨ k < r → IsZero (C.X r)) : {r | ¬ IsZero (C.X r)}.Finite :=
  (Set.finite_Icc 0 k).subset fun r hr => by
    by_contra h'
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at h'
    exact hr (h r (by omega))

private lemma strProd_add_left (P : DualityPairing B E B'') {C : ChainComplex B ℤ}
    {D : ChainComplex E ℤ} (hC : {r | ¬ IsZero (C.X r)}.Finite)
    (hD : {r | ¬ IsZero (D.X r)}.Finite) {m n : ℤ} (φ φ' : (StructureCx C).X m)
    (θ : (StructureCx D).X n) (k : ℤ) (hk : m + n = k) :
    strProd P hC hD (φ + φ') θ k hk = strProd P hC hD φ θ k hk + strProd P hC hD φ' θ k hk := by
  funext x
  show strProd P hC hD (φ + φ') θ k hk x =
    strProd P hC hD φ θ k hk x + strProd P hC hD φ' θ k hk x
  simp only [strProd, Pi.add_apply, P.map_add_left, Preadditive.add_comp, Preadditive.comp_add,
    smul_add, Finset.sum_add_distrib]

private lemma strProd_zero_left (P : DualityPairing B E B'') {C : ChainComplex B ℤ}
    {D : ChainComplex E ℤ} (hC : {r | ¬ IsZero (C.X r)}.Finite)
    (hD : {r | ¬ IsZero (D.X r)}.Finite) {m n : ℤ} (θ : (StructureCx D).X n) (k : ℤ)
    (hk : m + n = k) : strProd P hC hD (0 : (StructureCx C).X m) θ k hk = 0 := by
  have h := strProd_add_left P hC hD (0 : (StructureCx C).X m) 0 θ k hk
  rw [add_zero] at h
  simpa using h.symm

private lemma strProd_neg_left (P : DualityPairing B E B'') {C : ChainComplex B ℤ}
    {D : ChainComplex E ℤ} (hC : {r | ¬ IsZero (C.X r)}.Finite)
    (hD : {r | ¬ IsZero (D.X r)}.Finite) {m n : ℤ} (φ : (StructureCx C).X m)
    (θ : (StructureCx D).X n) (k : ℤ) (hk : m + n = k) :
    strProd P hC hD (-φ) θ k hk = -strProd P hC hD φ θ k hk := by
  refine eq_neg_of_add_eq_zero_left ?_
  rw [← strProd_add_left, neg_add_cancel, strProd_zero_left]

omit [Linear ℚ B] [DualCat B] in
private lemma finite_biprod {C C' : ChainComplex B ℤ} (hC : {r | ¬ IsZero (C.X r)}.Finite)
    (hC' : {r | ¬ IsZero (C'.X r)}.Finite) : {r | ¬ IsZero ((C ⊞ C').X r)}.Finite :=
  (hC.union hC').subset fun r hr => by
    by_contra h
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h
    refine hr (IsZero.of_iso ?_ (HomologicalComplex.biprodXIso C C' r))
    rw [IsZero.iff_id_eq_zero, ← biprod.total, h.1.eq_of_tgt biprod.fst 0,
      h.2.eq_of_tgt biprod.snd 0, zero_comp, zero_comp, add_zero]

private lemma push_push {C D D' : ChainComplex B ℤ} (g : C ⟶ D) (h : D ⟶ D') (n : ℤ)
    (x : (StructureCx C).X n) :
    (StructureCx.push h).f n ((StructureCx.push g).f n x) = (StructureCx.push (g ≫ h)).f n x := by
  rw [StructureCx.push_comp]
  rfl

private lemma push_id_apply (C : ChainComplex B ℤ) (n : ℤ) (x : (StructureCx C).X n) :
    (StructureCx.push (𝟙 C)).f n x = x := by
  rw [StructureCx.push_id]
  rfl

private lemma cxProdMap_comp (P : DualityPairing B E B'') {C C' C'' : ChainComplex B ℤ}
    {D D' D'' : ChainComplex E ℤ} (f : C ⟶ C') (f' : C' ⟶ C'') (g : D ⟶ D') (g' : D' ⟶ D'')
    (hC : {r | ¬ IsZero (C.X r)}.Finite) (hD : {r | ¬ IsZero (D.X r)}.Finite)
    (hC' : {r | ¬ IsZero (C'.X r)}.Finite) (hD' : {r | ¬ IsZero (D'.X r)}.Finite)
    (hC'' : {r | ¬ IsZero (C''.X r)}.Finite) (hD'' : {r | ¬ IsZero (D''.X r)}.Finite) :
    cxProdMap P (f ≫ f') (g ≫ g') hC hD hC'' hD'' =
      cxProdMap P f g hC hD hC' hD' ≫ cxProdMap P f' g' hC' hD' hC'' hD'' := by
  have := P.hasMapBifunctor_of_finite hC hD
  have := P.hasMapBifunctor_of_finite hC' hD'
  have := P.hasMapBifunctor_of_finite hC'' hD''
  ext j p q h
  simp only [HomologicalComplex.comp_f, HomologicalComplex.ι_mapBifunctorMap,
    HomologicalComplex.ι_mapBifunctorMap_assoc, Functor.curry_obj_map_app,
    Functor.curry_obj_obj_map, ← Functor.map_comp_assoc, CategoryTheory.prod_comp,
    Category.id_comp, Category.comp_id]

private lemma cxProdMap_id (P : DualityPairing B E B'') {C : ChainComplex B ℤ}
    {D : ChainComplex E ℤ} (hC : {r | ¬ IsZero (C.X r)}.Finite)
    (hD : {r | ¬ IsZero (D.X r)}.Finite) :
    cxProdMap P (𝟙 C) (𝟙 D) hC hD hC hD = 𝟙 _ := by
  have := P.hasMapBifunctor_of_finite hC hD
  ext j p q h
  simp

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

end General

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]

/-- The symmetric line has finitely many nonzero chain objects. -/
private lemma symLine_finite : {r | ¬ IsZero (symLine.X r)}.Finite :=
  finite_of_bounded (k := 1) fun r hr => symLine.isZero_X (by omega)

/-- A pair with boundary `(Z, ψ)` has a product with the line with boundary
`(Z ⊗ Λ, ψ ⊗ λ)`. -/
private lemma exists_prod_line_of_eq {j : ℕ} {m : ℤ}
    (W : SymPair (Karoubi (BoundedPow A j)) m (m + 1)) {Z : ChainComplex (Karoubi (BoundedPow A j)) ℤ}
    {ψ : (StructureCx Z).X m}
    (hW : (⟨W.C, W.φ⟩ : Σ C : ChainComplex (Karoubi (BoundedPow A j)) ℤ, (StructureCx C).X m) =
      ⟨Z, ψ⟩) (hZ : {r | ¬ IsZero (Z.X r)}.Finite) :
    ∃ (W' : SymPair (Karoubi (BoundedPow A (j + 1))) (m + 1) (m + 1 + 1))
      (D' : ChainComplex (Karoubi (BoundedPow A (j + 1))) ℤ)
      (f' : cxProd (boxPairingPow A j) Z symLine hZ symLine_finite ⟶ D')
      (δ' : (StructureCx D').X (m + 1 + 1)),
      W'.data = ⟨cxProd (boxPairingPow A j) Z symLine hZ symLine_finite, D', f', δ',
        strProd (boxPairingPow A j) hZ symLine_finite ψ symLine.str (m + 1) rfl⟩ := by
  cases hW
  obtain ⟨W', hW'⟩ := SymPair.exists_prod_line W hZ (finite_of_bounded W.bounded) symLine_finite
  exact ⟨W', _, _, _, hW'⟩

/-- Pair transport, for a pair given through its data. -/
private lemma transport_of_data {B : Type*} [Category B] [Preadditive B] [Linear ℚ B]
    [HasFiniteBiproducts B] [DualCat B] {m n : ℤ} (W : SymPair B m n) {C C' D : ChainComplex B ℤ}
    {f : C ⟶ D} {δφ : (StructureCx D).X n} {φ : (StructureCx C).X m}
    (h : W.data = ⟨C, D, f, δφ, φ⟩) (u : C' ≅ C) (φ' : (StructureCx C').X m)
    (hφ' : (StructureCx.push u.hom).f m φ' = φ) :
    ∃ W' : SymPair B m n, W'.data = ⟨C', D, u.hom ≫ f, δφ, φ'⟩ := by
  cases h
  obtain ⟨W', hW'⟩ := W.transport u φ' hφ' 1
  rw [one_smul, one_smul] at hW'
  exact ⟨W', hW'⟩

/-- Cobordant complexes have cobordant products with the line. -/
private theorem transitionCx_cobordant {j : ℕ} {m m' : ℤ} (hm : m + 1 = m')
    {x y : SymPoincare (Karoubi (BoundedPow A j)) m} (h : Cobordant x y) :
    Cobordant (transitionCx hm x) (transitionCx hm y) := by
  subst hm
  obtain ⟨W, hW⟩ := h
  have hx := finite_of_bounded x.bounded
  have hy := finite_of_bounded y.bounded
  have hxy := finite_biprod hx hy
  obtain ⟨W', D', f', δ', hW'⟩ := exists_prod_line_of_eq W hW hxy
  obtain ⟨W'', hW''⟩ := transport_of_data W' hW' (sumIso (boxPairingPow A j) hx hy hxy symLine_finite)
    (StructureCx.sum (transitionCx rfl x).φ (-(transitionCx rfl y).φ)) (by
      rw [show -(transitionCx rfl y).φ = strProd (boxPairingPow A j) hy symLine_finite (-y.φ)
        symLine.str (m + 1) rfl from (strProd_neg_left _ hy _ y.φ _ _ rfl).symm]
      exact push_sumIso _ hx hy hxy symLine_finite x.φ (-y.φ) symLine.str (m + 1) rfl)
  exact Cobordant.of_data_eq W'' hW''

/-- The product with the line of a structured complex `z` with `(z.C, z.φ) = (Z, ψ)` has the
class of `w` when an isomorphism carries `(w.C, w.φ)` to `(Z ⊗ Λ, ψ ⊗ λ)`. -/
private lemma mk_transitionCx_eq {j : ℕ} {m : ℤ} (z : SymPoincare (Karoubi (BoundedPow A j)) m)
    {Z : ChainComplex (Karoubi (BoundedPow A j)) ℤ} {ψ : (StructureCx Z).X m}
    (hz : (⟨z.C, z.φ⟩ : Σ C : ChainComplex (Karoubi (BoundedPow A j)) ℤ, (StructureCx C).X m) =
      ⟨Z, ψ⟩) (hZ : {r | ¬ IsZero (Z.X r)}.Finite)
    (w : SymPoincare (Karoubi (BoundedPow A (j + 1))) (m + 1))
    {Z' : ChainComplex (Karoubi (BoundedPow A (j + 1))) ℤ} {ψ' : (StructureCx Z').X (m + 1)}
    (hw : (⟨w.C, w.φ⟩ : Σ C : ChainComplex (Karoubi (BoundedPow A (j + 1))) ℤ,
      (StructureCx C).X (m + 1)) = ⟨Z', ψ'⟩)
    (u : Z' ≅ cxProd (boxPairingPow A j) Z symLine hZ symLine_finite)
    (hu : (StructureCx.push u.hom).f (m + 1) ψ' =
      strProd (boxPairingPow A j) hZ symLine_finite ψ symLine.str (m + 1) rfl) :
    LGroup.mk (transitionCx rfl z) = LGroup.mk w := by
  cases hz
  cases hw
  refine (LGroup.mk_eq_of_homotopyIsometry w (transitionCx rfl z) (HomotopyEquiv.ofIso u) 0 ?_).symm
  rw [map_zero]
  change 0 = (StructureCx.push u.hom).f (m + 1) w.φ - _
  rw [hu]
  exact (sub_self _).symm

/-- The product with the line of a sum is homotopy-isometric to the sum of the products. -/
private theorem transitionCx_sum {j : ℕ} {m m' : ℤ} (hm : m + 1 = m')
    (x y : SymPoincare (Karoubi (BoundedPow A j)) m) :
    LGroup.mk (transitionCx hm (x.sum y)) =
      LGroup.mk ((transitionCx hm x).sum (transitionCx hm y)) := by
  subst hm
  have hx := finite_of_bounded x.bounded
  have hy := finite_of_bounded y.bounded
  have hxy := finite_biprod hx hy
  exact mk_transitionCx_eq (x.sum y) (SymPoincare.sum_spec x y) hxy _
    (SymPoincare.sum_spec (transitionCx rfl x) (transitionCx rfl y))
    (sumIso (boxPairingPow A j) hx hy hxy symLine_finite)
    (push_sumIso _ hx hy hxy symLine_finite x.φ y.φ symLine.str (m + 1) rfl)

/-- **Transition map.** `t : L^p_m(C_{ℤ^j} A) → L^p_{m'}(C_{ℤ^{j+1}} A)`,
`[C, φ] ↦ [C ⊗ Λ, φ ⊗ λ]` (`m' = m + 1`), a homomorphism. -/
noncomputable def transitionMap (A : Type u) [Category.{v} A] [Preadditive A] [Linear ℚ A]
    [HasFiniteBiproducts A] [DualCat A] (j : ℕ) {m m' : ℤ} (hm : m + 1 = m') :
    Lp (BoundedPow A j) m →+ Lp (BoundedPow A (j + 1)) m' :=
  AddMonoidHom.mk' (Quotient.lift (fun x => LGroup.mk (transitionCx hm x))
    fun _ _ h => Quotient.sound (transitionCx_cobordant hm h)) fun a b => by
    induction a using Quotient.ind
    induction b using Quotient.ind
    exact transitionCx_sum hm _ _

/-- The value of `t` on a class: `t [C, φ] = [C ⊗ Λ, φ ⊗ λ]`. -/
lemma transitionMap_mk (j : ℕ) {m m' : ℤ} (hm : m + 1 = m')
    (x : SymPoincare (Karoubi (BoundedPow A j)) m) :
    transitionMap A j hm (LGroup.mk x) = LGroup.mk (transitionCx hm x) :=
  rfl

end HSP
