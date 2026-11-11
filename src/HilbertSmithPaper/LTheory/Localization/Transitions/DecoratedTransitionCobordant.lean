import Mathlib
import HilbertSmithPaper.LTheory.Base.Pairs.Cobordism
import HilbertSmithPaper.LTheory.Localization.Transitions.DecoratedLineProduct
import HilbertSmithPaper.LTheory.Localization.Decorations.SubcategoryCobordism
import HilbertSmithPaper.LTheory.Localization.Products.ProductWithLine
import HilbertSmithPaper.LTheory.Localization.Products.ProductSum
import HilbertSmithPaper.LTheory.Localization.Products.ProductPush
import HilbertSmithPaper.LTheory.Base.Pairs.FunctorPair

/-!
# The decorated transition respects cobordism

For an involution-invariant Karoubi filtration `𝒰 ⊂ 𝒜`, cobordant strict symmetric Poincaré
complexes in `Kar C_{ℤ^j}(𝒜/𝒰)` have cobordant decorated products with the line in
`Dec(C_{ℤ^{j+1}}𝒜/C_{ℤ^{j+1}}𝒰)`.

A cobordism `W` between them has a product with the line, whose image under `e_{j+1}^{-1}` has
decorated codomain and boundary isomorphic to the sum of the decorated products; cobordisms in a
full subcategory give the claim.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

namespace HSP

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A] {U : ObjectProperty A} [IsDualAdditive U]

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

private lemma push_comp_apply'' {V : Type*} [Category V] [Preadditive V] [Linear ℚ V]
    [HasFiniteBiproducts V] [DualCat V] {C D E : ChainComplex V ℤ} (f : C ⟶ D) (g : D ⟶ E)
    (n : ℤ) (φ : (StructureCx C).X n) :
    (StructureCx.push (f ≫ g)).f n φ = (StructureCx.push g).f n ((StructureCx.push f).f n φ) := by
  rw [StructureCx.push_comp]
  rfl

private lemma push_inv_hom'' {V : Type*} [Category V] [Preadditive V] [Linear ℚ V]
    [HasFiniteBiproducts V] [DualCat V] {C D : ChainComplex V ℤ} (u : C ≅ D) (n : ℤ)
    (φ : (StructureCx C).X n) :
    (StructureCx.push u.inv).f n ((StructureCx.push u.hom).f n φ) = φ := by
  rw [← push_comp_apply'', u.hom_inv_id, StructureCx.push_id]
  rfl

private lemma iso_of_sigma_eq'' {V : Type*} [Category V] [Preadditive V] [Linear ℚ V]
    [HasFiniteBiproducts V] [DualCat V] {k : ℤ} {C₀ C : ChainComplex V ℤ}
    {φ₀ : (StructureCx C₀).X k} {φ : (StructureCx C).X k}
    (h : (⟨C₀, φ₀⟩ : Σ C : ChainComplex V ℤ, (StructureCx C).X k) = ⟨C, φ⟩) :
    ∃ u : C ≅ C₀, (StructureCx.push u.hom).f k φ = φ₀ := by
  obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp h
  obtain rfl := eq_of_heq h
  exact ⟨Iso.refl _, by rw [Iso.refl_hom, StructureCx.push_id]; rfl⟩

private lemma incl_mapStructure_decTransitionCx (F : KaroubiFiltration U) (j : ℕ) {m : ℤ}
    (z : SymPoincare (Karoubi (BoundedPow (FiltQuot U) j)) m) :
    (DualSubcategory.incl (IsDecorated (Bounded.subPow U (j + 1)))).mapStructure _ (m + 1)
      (decTransitionCx F j rfl z).φ =
      (Bounded.powQuotientIso F (j + 1)).1.2.kar.mapStructure _ (m + 1) (transitionCx rfl z).φ :=
  funext fun i => Category.id_comp
    (((Bounded.powQuotientIso F (j + 1)).1.2.kar.mapStructure _ (m + 1) (transitionCx rfl z).φ) i)

private lemma map_prod_line_decorated (F : KaroubiFiltration U) (j : ℕ) {k : ℤ}
    (W' : SymPair (Karoubi (BoundedPow (FiltQuot U) (j + 1))) k (k + 1))
    (D : ChainComplex (Karoubi (BoundedPow (FiltQuot U) j)) ℤ)
    (hD : {r | ¬ IsZero (D.X r)}.Finite) (hΛ : {r | ¬ IsZero (symLine.X r)}.Finite)
    (hd : W'.D = cxProd (boxPairingPow (FiltQuot U) j) D symLine hD hΛ) (r : ℤ) :
    IsDecorated (Bounded.subPow U (j + 1))
      ((SymPair.map (Bounded.powQuotientIso F (j + 1)).1.2.kar W').D.X r) := by
  have h2 := (cxProd_line_decorated F j D hD hΛ r).2
  rw [← hd] at h2
  exact h2


/-- **The decorated transition respects cobordism.** -/
theorem decTransitionCx_cobordant (F : KaroubiFiltration U) (j : ℕ) {m m' : ℤ} (hm : m + 1 = m')
    {x y : SymPoincare (Karoubi (BoundedPow (FiltQuot U) j)) m} (h : Cobordant x y) :
    Cobordant (decTransitionCx F j hm x) (decTransitionCx F j hm y) := by
  subst hm
  obtain ⟨W, hW⟩ := h
  obtain ⟨a, ha⟩ := iso_of_sigma_eq'' hW
  have hx := finite_of_bounded x.bounded
  have hy := finite_of_bounded y.bounded
  have hC : {r | ¬ IsZero (W.C.X r)}.Finite := finite_of_bounded W.boundary.bounded
  have hxy : {r | ¬ IsZero ((x.C ⊞ y.C).X r)}.Finite :=
    hC.subset fun r hr h => hr (h.of_iso ((HomologicalComplex.eval _ _ r).mapIso a))
  have hD := finite_of_bounded W.bounded
  have hΛ : {r | ¬ IsZero (symLine.X r)}.Finite :=
    finite_of_bounded (k := 1) fun r hr => symLine.isZero_X (by omega)
  let Pp := boxPairingPow (FiltQuot U) j
  obtain ⟨W', hW'⟩ := SymPair.exists_prod_line W hC hD hΛ
  obtain ⟨b, hb⟩ := iso_of_sigma_eq'' (congrArg (fun d : SymPair.Data _ (m + 1) (m + 1 + 1) =>
    (⟨d.1, d.2.2.2.2⟩ : Σ C : ChainComplex (Karoubi (BoundedPow (FiltQuot U) (j + 1))) ℤ,
      (StructureCx C).X (m + 1))) hW')
  let c : cxProd Pp (x.C ⊞ y.C) symLine hxy hΛ ≅ cxProd Pp W.C symLine hC hΛ :=
    { hom := cxProdMap Pp a.hom (𝟙 _) hxy hΛ hC hΛ
      inv := cxProdMap Pp a.inv (𝟙 _) hC hΛ hxy hΛ
      hom_inv_id := by rw [← cxProdMap_comp, a.hom_inv_id, Category.comp_id, cxProdMap_id]
      inv_hom_id := by rw [← cxProdMap_comp, a.inv_hom_id, Category.comp_id, cxProdMap_id] }
  obtain ⟨u₁, hu₁⟩ := cxProd_sum_iso Pp hx hy hxy hΛ x.φ (-y.φ) symLine.str (m + 1) rfl
  have hneg : strProd Pp hy hΛ (-y.φ) symLine.str (m + 1) rfl =
      -strProd Pp hy hΛ y.φ symLine.str (m + 1) rfl := by
    refine eq_neg_of_add_eq_zero_left ?_
    rw [← strProd_add_left, neg_add_cancel]
    have h0 := strProd_add_left Pp hy hΛ (0 : (StructureCx y.C).X m) 0 symLine.str (m + 1) rfl
    rw [add_zero] at h0
    simpa using h0.symm
  let w : cxProd Pp x.C symLine hx hΛ ⊞ cxProd Pp y.C symLine hy hΛ ≅ W'.C := u₁.symm ≪≫ c ≪≫ b
  have hw : (StructureCx.push w.hom).f (m + 1)
      (StructureCx.sum (strProd Pp hx hΛ x.φ symLine.str (m + 1) rfl)
        (-strProd Pp hy hΛ y.φ symLine.str (m + 1) rfl)) = W'.φ := by
    have h1 : (StructureCx.push u₁.inv).f (m + 1)
        (StructureCx.sum (strProd Pp hx hΛ x.φ symLine.str (m + 1) rfl)
          (-strProd Pp hy hΛ y.φ symLine.str (m + 1) rfl)) =
        strProd Pp hxy hΛ (StructureCx.sum x.φ (-y.φ)) symLine.str (m + 1) rfl := by
      rw [← hneg, ← hu₁, push_inv_hom'']
    have h2 : (StructureCx.push c.hom).f (m + 1)
        (strProd Pp hxy hΛ (StructureCx.sum x.φ (-y.φ)) symLine.str (m + 1) rfl) =
        strProd Pp hC hΛ W.φ symLine.str (m + 1) rfl := by
      change (StructureCx.push (cxProdMap Pp a.hom (𝟙 _) hxy hΛ hC hΛ)).f (m + 1) _ = _
      rw [strProd_push, ha, StructureCx.push_id]
      rfl
    change (StructureCx.push (u₁.inv ≫ c.hom ≫ b.hom)).f (m + 1) _ = _
    rw [push_comp_apply'', h1, push_comp_apply'', h2]
    exact hb
  let G := (Bounded.powQuotientIso F (j + 1)).1.2.kar
  let Gm := G.toFunctor.mapHomologicalComplex (ComplexShape.down ℤ)
  have e := incl_mapStructure_decTransitionCx F j (m := m)
  refine SymPoincare.cobordant_of_pair (IsDecorated (Bounded.subPow U (j + 1))) _ _
    (SymPair.map G W') ((Gm.mapBiprod _ _).symm ≪≫ Gm.mapIso w) ?_ ?_
  · erw [e x, e y, ← map_neg]
    change (StructureCx.push ((Gm.mapBiprod (cxProd Pp x.C symLine hx hΛ)
        (cxProd Pp y.C symLine hy hΛ)).inv ≫ Gm.map w.hom)).f (m + 1)
      (StructureCx.sum (G.mapStructure _ (m + 1) (strProd Pp hx hΛ x.φ symLine.str (m + 1) rfl))
        (G.mapStructure _ (m + 1) (-strProd Pp hy hΛ y.φ symLine.str (m + 1) rfl))) =
      G.mapStructure W'.C (m + 1) W'.φ
    rw [push_comp_apply'', DualFunctor.mapStructure_sum, ← DualFunctor.mapStructure_pushforward, hw]
  · exact map_prod_line_decorated F j W' W.D hD hΛ
      (congrArg (fun d : SymPair.Data _ (m + 1) (m + 1 + 1) => d.2.1) hW')

end HSP
