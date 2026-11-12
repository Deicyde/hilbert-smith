import Mathlib
import HilbertSmithPaper.LTheory.Base.Groups.LGroupAdd
import HilbertSmithPaper.LTheory.Base.Complexes.FiniteBounded
import HilbertSmithPaper.LTheory.Base.Complexes.FunctorPush
import HilbertSmithPaper.LTheory.Base.Complexes.Functors.FunctorStructureSum
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
decorated objects then give the claim (`HSP.SymPoincare.mk_eq_add_of_sumIso`).
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

end Push

/-- The image of `x.toSub` under the inclusion carries the structure of `x`. -/
private lemma mapStructure_toSub {B : Type*} [Category B] [Preadditive B] [Linear ℚ B]
    [HasFiniteBiproducts B] [DualCat B] {P : ObjectProperty B} [IsDualAdditive P] {k : ℤ}
    (x : SymPoincare B k) (hx : ∀ r, P (x.C.X r)) :
    (DualSubcategory.incl P).mapStructure _ k (x.toSub P hx).φ = x.φ :=
  funext fun _ => Category.id_comp _

/-- Sums in a full subcategory, for complexes given in `ℬ`. -/
private lemma mk_toSub_eq_add {B : Type*} [Category B] [Preadditive B] [Linear ℚ B]
    [HasFiniteBiproducts B] [DualCat B] (P : ObjectProperty B) [IsDualAdditive P] {k : ℤ}
    (z x y : SymPoincare B k) (hz : ∀ r, P (z.C.X r)) (hx : ∀ r, P (x.C.X r))
    (hy : ∀ r, P (y.C.X r)) (u : z.C ≅ x.C ⊞ y.C)
    (hu : (StructureCx.push u.hom).f k z.φ = StructureCx.sum x.φ y.φ) :
    LGroup.mk (z.toSub P hz) = LGroup.mk (x.toSub P hx) + LGroup.mk (y.toSub P hy) :=
  SymPoincare.mk_eq_add_of_sumIso P _ _ _ u (by
    rw [mapStructure_toSub, mapStructure_toSub, mapStructure_toSub]
    exact hu)

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
  have key1 := DualFunctor.mapStructure_sum G (transitionCx hm x).C (transitionCx hm y).C m'
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
  exact mk_toSub_eq_add (IsDecorated (Bounded.subPow U (j + 1))) z a b _ _ _ u hu

end HSP
