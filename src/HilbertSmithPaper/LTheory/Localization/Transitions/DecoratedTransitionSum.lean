import Mathlib
import HilbertSmithPaper.LTheory.Base.Groups.LGroupAdd
import HilbertSmithPaper.LTheory.Base.Complexes.FiniteBounded
import HilbertSmithPaper.LTheory.Base.Complexes.FunctorPush
import HilbertSmithPaper.LTheory.Base.Pairs.PoincareSum
import HilbertSmithPaper.LTheory.Localization.Decorations.SubcategorySum
import HilbertSmithPaper.LTheory.Localization.Products.ProductSum
import HilbertSmithPaper.LTheory.Localization.Transitions.DecoratedLineProduct

/-!
# The decorated transition is additive

For an involution-invariant Karoubi filtration `𝒰 ⊂ 𝒜`, the decorated product with the line of a
sum `(C ⊕ C', φ ⊕ φ')` has the class of the sum of the decorated products in
`L^{im}(C_{ℤ^{j+1}}𝒜/C_{ℤ^{j+1}}𝒰)`.

The isomorphism `(C ⊕ C') ⊗ Λ ≅ C ⊗ Λ ⊕ C' ⊗ Λ` carrying `(φ ⊕ φ') ⊗ λ` to
`φ ⊗ λ ⊕ φ' ⊗ λ` (`HSP.cxProd_sum_iso`, composed with the identification of the chosen sum with
`C ⊕ C'`) is carried by `e_{j+1}^{-1}` to an isomorphism onto the sum of the images, which carries
the structures (`HSP.DualFunctor.mapStructure_pushforward`). Sums in the full subcategory of
decorated objects then give the claim (`HSP.SymPoincare.mk_toSub_of_sumIso`).
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

namespace HSP

universe v u

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

section Push

variable {V : Type*} [Category V] [Preadditive V] [Linear ℚ V] [HasFiniteBiproducts V]
  [DualCat V]

private lemma push_comp_apply {C D E : ChainComplex V ℤ} (f : C ⟶ D) (g : D ⟶ E) (n : ℤ)
    (φ : (StructureCx C).X n) :
    (StructureCx.push (f ≫ g)).f n φ = (StructureCx.push g).f n ((StructureCx.push f).f n φ) := by
  rw [StructureCx.push_comp]
  rfl

private lemma push_id_apply (C : ChainComplex V ℤ) (n : ℤ) (φ : (StructureCx C).X n) :
    (StructureCx.push (𝟙 C)).f n φ = φ := by
  rw [StructureCx.push_id]
  rfl

private lemma push_inv_hom {C D : ChainComplex V ℤ} (u : C ≅ D) (n : ℤ)
    (φ : (StructureCx C).X n) : (StructureCx.push u.inv).f n ((StructureCx.push u.hom).f n φ) = φ := by
  rw [← push_comp_apply, u.hom_inv_id, push_id_apply]

private lemma push_mapBiprod_inv {W : Type*} [Category W] [Preadditive W] [Linear ℚ W]
    [HasFiniteBiproducts W] [DualCat W] (Fd : DualFunctor V W) (X Y : ChainComplex V ℤ) (n : ℤ)
    (φ : (StructureCx X).X n) (ψ : (StructureCx Y).X n) :
    (StructureCx.push ((Fd.toFunctor.mapHomologicalComplex (ComplexShape.down ℤ)).mapBiprod
      X Y).inv).f n (StructureCx.sum (Fd.mapStructure X n φ) (Fd.mapStructure Y n ψ)) =
      Fd.mapStructure (X ⊞ Y) n (StructureCx.sum φ ψ) := by
  unfold StructureCx.sum
  rw [Functor.mapBiprod_inv, map_add, map_add, ← push_comp_apply, ← push_comp_apply,
    biprod.inl_desc, biprod.inr_desc, DualFunctor.mapStructure_pushforward,
    DualFunctor.mapStructure_pushforward]

end Push

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A] {U : ObjectProperty A} [IsDualAdditive U]

/-- **The decorated transition is additive.** -/
theorem decTransitionCx_sum (F : KaroubiFiltration U) (j : ℕ) {m m' : ℤ} (hm : m + 1 = m')
    (x y : SymPoincare (Karoubi (BoundedPow (FiltQuot U) j)) m) :
    LGroup.mk (decTransitionCx F j hm (x.sum y)) =
      LGroup.mk ((decTransitionCx F j hm x).sum (decTransitionCx F j hm y)) := by
  have hx := finite_of_bounded x.bounded
  have hy := finite_of_bounded y.bounded
  have hs := finite_of_bounded (x.sum y).bounded
  have hΛ : {r | ¬ IsZero (symLine.X r)}.Finite :=
    finite_of_bounded (k := 1) fun r hr => symLine.isZero_X (by omega)
  obtain ⟨w, hw⟩ := SymPoincare.exists_sum_iso x y
  have hxy : {r | ¬ IsZero ((x.C ⊞ y.C).X r)}.Finite :=
    hs.subset fun r hr h => hr (h.of_iso ((HomologicalComplex.eval _ _ r).mapIso w))
  let P := boxPairingPow (FiltQuot U) j
  let c : cxProd P (x.sum y).C symLine hs hΛ ≅ cxProd P (x.C ⊞ y.C) symLine hxy hΛ :=
    { hom := cxProdMap P w.inv (𝟙 _) hs hΛ hxy hΛ
      inv := cxProdMap P w.hom (𝟙 _) hxy hΛ hs hΛ
      hom_inv_id := by rw [← cxProdMap_comp, w.inv_hom_id, Category.comp_id, cxProdMap_id]
      inv_hom_id := by rw [← cxProdMap_comp, w.hom_inv_id, Category.comp_id, cxProdMap_id] }
  obtain ⟨u₁, hu₁⟩ := cxProd_sum_iso P hx hy hxy hΛ x.φ y.φ symLine.str m' (by omega)
  have hv₀ : (StructureCx.push (c ≪≫ u₁).hom).f m'
      (strProd P hs hΛ (x.sum y).φ symLine.str m' (by omega)) =
      StructureCx.sum (strProd P hx hΛ x.φ symLine.str m' (by omega))
        (strProd P hy hΛ y.φ symLine.str m' (by omega)) := by
    rw [Iso.trans_hom, push_comp_apply]
    change (StructureCx.push u₁.hom).f m' ((StructureCx.push (cxProdMap P w.inv (𝟙 _) hs hΛ hxy hΛ)).f m' _) = _
    rw [strProd_push, push_id_apply, ← hw, push_inv_hom, hu₁]
  let v : (transitionCx hm (x.sum y)).C ≅ (transitionCx hm x).C ⊞ (transitionCx hm y).C := c ≪≫ u₁
  have hv : (StructureCx.push v.hom).f m' (transitionCx hm (x.sum y)).φ =
      StructureCx.sum (transitionCx hm x).φ (transitionCx hm y).φ := hv₀
  let G := (Bounded.powQuotientIso F (j + 1)).1.2.kar
  let z := SymPoincare.map G (transitionCx hm (x.sum y))
  let a := SymPoincare.map G (transitionCx hm x)
  let b := SymPoincare.map G (transitionCx hm y)
  let u : z.C ≅ a.C ⊞ b.C := (G.toFunctor.mapHomologicalComplex (ComplexShape.down ℤ)).mapIso v ≪≫
    (G.toFunctor.mapHomologicalComplex (ComplexShape.down ℤ)).mapBiprod (transitionCx hm x).C (transitionCx hm y).C
  have key1 := push_mapBiprod_inv G (transitionCx hm x).C (transitionCx hm y).C m'
    (transitionCx hm x).φ (transitionCx hm y).φ
  have key2 : (StructureCx.push v.inv).f m'
      (StructureCx.sum (transitionCx hm x).φ (transitionCx hm y).φ) =
      (transitionCx hm (x.sum y)).φ :=
    (congrArg ((StructureCx.push v.inv).f m') hv).symm.trans (push_inv_hom _ _ _)
  have hinv : (StructureCx.push u.inv).f m' (StructureCx.sum a.φ b.φ) = z.φ := by
    change (StructureCx.push (((G.toFunctor.mapHomologicalComplex (ComplexShape.down ℤ)).mapBiprod
        (transitionCx hm x).C (transitionCx hm y).C).inv ≫
        (G.toFunctor.mapHomologicalComplex (ComplexShape.down ℤ)).map v.inv)).f m'
      (StructureCx.sum (G.mapStructure _ m' (transitionCx hm x).φ)
        (G.mapStructure _ m' (transitionCx hm y).φ)) =
      G.mapStructure _ m' (transitionCx hm (x.sum y)).φ
    rw [push_comp_apply, key1, ← DualFunctor.mapStructure_pushforward, key2]
  have hu : (StructureCx.push u.hom).f m' z.φ = StructureCx.sum a.φ b.φ := by
    rw [← hinv, ← push_comp_apply, u.inv_hom_id, push_id_apply]
  rw [← LGroup.mk_add]
  exact SymPoincare.mk_toSub_of_sumIso (IsDecorated (Bounded.subPow U (j + 1))) z a b _ _ _ u hu

end HSP
