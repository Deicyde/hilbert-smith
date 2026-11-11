import HilbertSmithPaper.Categories.Supports.QuotientSupportAdditive
import HilbertSmithPaper.Categories.Supports.NullThickening
import HilbertSmithPaper.Categories.Asymptotic.Restriction.ProjectionInclusion
import HilbertSmithPaper.Categories.Asymptotic.Restriction.DiagonalProjectionComplement

/-!
# Iterated quotient

For `S, Y, Z ⊆ X`, the identity on objects and on representatives gives mutually inverse strict
duality functors `(𝒜_S/𝒜_Z)/𝒰_Y ≅ 𝒜_S/𝒜_{Y ∪ Z}` commuting with the quotient functors from `𝒜_S`
(`HSP.iteratedQuotient`, a subtype of pairs of duality functors). The outer quotient is by the
predicate `𝒰_Y = HSP.quotSupp S Z Y` of the quotient support filtration.

The key step (`HSP.ideal_union_split`): a map of `𝒜_S` factoring through a `(Y ∪ Z)`-supported
`W` is a sum of a map through a `Y`-supported object and a map through a `Z`-supported one: for a
null `r` with the labels of `W` eventually in `N̄_{r_i}(Y ∪ Z)`, split `W` into the indices with
labels in `N̄_{r_i}(Y)` and the rest, whose labels eventually lie in `N̄_{r_i}(Z)`. Hence
`I_Y + I_Z = I_{Y ∪ Z}`. No disjointness, closedness or invariance is used.
-/

open CategoryTheory CategoryTheory.Limits Filter Metric Topology
open scoped NNReal

namespace HSP

open DualCat

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

/-- The indices `k` with `x_i(k)` in the closed `r_i`-thickening of `Y`. -/
private def nearIdx (Y : Set X) (M : AsymPre G X) (r : ℕ → ℝ≥0) : ∀ i, Fin (M.n i) → Prop :=
  fun i k => M.x i k ∈ cthickening (r i) Y

private theorem supp_restrict {S : Set X} {M : AsymPre G X} (hM : supp S (⟨M⟩ : AsymCat G X))
    (P : ∀ i, Fin (M.n i) → Prop) : supp S (⟨M.restrict P⟩ : AsymCat G X) := fun ε hε =>
  (hM ε hε).mono fun _ h _ => h _

private theorem supp_restrict_near {Y : Set X} {M : AsymPre G X} {r : ℕ → ℝ≥0}
    (hr : Tendsto r atTop (𝓝 0)) : supp Y (⟨M.restrict (nearIdx Y M r)⟩ : AsymCat G X) := by
  intro ε hε
  filter_upwards [(NNReal.tendsto_coe.2 hr).eventually (gt_mem_nhds hε)] with i hi k
  exact cthickening_subset_thickening' hε hi Y (AsymPre.restrictEmb_mem k)

/-- The ideal of maps of `𝒜_S` through `𝒜_Z` is monotone in `Z`. -/
private theorem ideal_suppIn_mono {S Z Z' : Set X} (h : Z ⊆ Z')
    {M N : (supp S : ObjectProperty (AsymCat G X)).FullSubcategory} {f : M ⟶ N}
    (hf : FiltQuot.ideal (suppIn S Z) f) : FiltQuot.ideal (suppIn S Z') f := by
  obtain ⟨V, hV, a, b, rfl⟩ := hf
  exact ⟨V, fun ε hε => (hV ε hε).mono fun _ hi k => thickening_subset_of_subset ε h (hi k),
    a, b, rfl⟩

/-- `I_{Y ∪ Z} ⊆ I_Y + I_Z` in `𝒜_S`. -/
private theorem ideal_union_split {S Y Z : Set X}
    {M N : (supp S : ObjectProperty (AsymCat G X)).FullSubcategory} {f : M ⟶ N}
    (hf : FiltQuot.ideal (suppIn S (Y ∪ Z)) f) :
    ∃ y z, FiltQuot.ideal (suppIn S Y) y ∧ FiltQuot.ideal (suppIn S Z) z ∧ f = y + z := by
  classical
  obtain ⟨W, hW, a, b, rfl⟩ := hf
  obtain ⟨r, hr, hev⟩ := exists_null_cthickening (M := W.obj.as) (Y ∪ Z) (fun _ _ => True)
    (fun ε hε => (hW ε hε).mono fun _ hi k _ => hi k)
  let P := nearIdx Y W.obj.as r
  let Wy : (supp S : ObjectProperty (AsymCat G X)).FullSubcategory :=
    ⟨⟨W.obj.as.restrict P⟩, supp_restrict W.property _⟩
  let Wz : (supp S : ObjectProperty (AsymCat G X)).FullSubcategory :=
    ⟨⟨W.obj.as.restrict (fun i k => ¬P i k)⟩, supp_restrict W.property _⟩
  let iy : Wy ⟶ W := ObjectProperty.homMk (AsymCat.mkHom (AsymPre.restrictInc _ _))
  let py : W ⟶ Wy := ObjectProperty.homMk (AsymCat.mkHom (AsymPre.restrictPro _ _))
  let iz : Wz ⟶ W := ObjectProperty.homMk (AsymCat.mkHom (AsymPre.restrictInc _ _))
  let pz : W ⟶ Wz := ObjectProperty.homMk (AsymCat.mkHom (AsymPre.restrictPro _ _))
  have htot : py ≫ iy + pz ≫ iz = 𝟙 W := by
    refine ObjectProperty.hom_ext _ ?_
    change AsymCat.mkHom (AsymPre.restrictPro _ _) ≫ AsymCat.mkHom (AsymPre.restrictInc _ _) +
      AsymCat.mkHom (AsymPre.restrictPro _ _) ≫ AsymCat.mkHom (AsymPre.restrictInc _ _) =
        𝟙 W.obj
    rw [← Functor.map_comp, ← Functor.map_comp, AsymPre.restrictPro_restrictInc,
      AsymPre.restrictPro_restrictInc, AsymPre.trunc_not, ← Functor.map_add, add_sub_cancel,
      CategoryTheory.Functor.map_id]
    rfl
  refine ⟨a ≫ py ≫ iy ≫ b, a ≫ pz ≫ iz ≫ b, ⟨Wy, supp_restrict_near hr, a ≫ py, iy ≫ b,
    by simp only [Category.assoc]⟩, ⟨Wz, ?_, a ≫ pz, iz ≫ b, by simp only [Category.assoc]⟩, ?_⟩
  · intro ε hε
    filter_upwards [hev, (NNReal.tendsto_coe.2 hr).eventually (gt_mem_nhds hε)] with i hi hri k
    have hk := AsymPre.restrictEmb_mem (P := fun i k => ¬P i k) k
    have h := hi (W.obj.as.restrictEmb (fun i k => ¬P i k) i k) trivial
    rw [cthickening_union] at h
    exact cthickening_subset_thickening' hε hri Z (h.resolve_left hk)
  · rw [← Preadditive.comp_add, ← Category.assoc py, ← Category.assoc pz,
      ← Preadditive.add_comp, htot, Category.id_comp]

section Lift

variable {A : Type*} [Category A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A] {B : Type*} [Category B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B] (U : ObjectProperty A) [IsDualAdditive U]

/-- The functor `𝒜/𝒰 → ℬ` induced by a functor `𝒜 → ℬ` killing the ideal of `𝒰`. -/
private abbrev liftFun (F : A ⥤ B)
    (H : ∀ (x y : A) (f₁ f₂ : x ⟶ y), FiltQuot.rel U f₁ f₂ → F.map f₁ = F.map f₂) :
    FiltQuot U ⥤ B :=
  CategoryTheory.Quotient.lift (FiltQuot.rel U) F H

private instance (F : A ⥤ B) [F.Additive]
    (H : ∀ (x y : A) (f₁ f₂ : x ⟶ y), FiltQuot.rel U f₁ f₂ → F.map f₁ = F.map f₂) :
    (liftFun U F H).Additive where
  map_add {_ _ f g} := by
    obtain ⟨f, rfl⟩ := FiltQuot.functor_map_surjective U f
    obtain ⟨g, rfl⟩ := FiltQuot.functor_map_surjective U g
    rw [← Functor.map_add, CategoryTheory.Quotient.lift_map_functor_map,
      CategoryTheory.Quotient.lift_map_functor_map,
      CategoryTheory.Quotient.lift_map_functor_map, Functor.map_add]

private instance (F : A ⥤ B) [F.Linear ℚ]
    (H : ∀ (x y : A) (f₁ f₂ : x ⟶ y), FiltQuot.rel U f₁ f₂ → F.map f₁ = F.map f₂) :
    (liftFun U F H).Linear ℚ where
  map_smul {_ _} f c := by
    obtain ⟨f, rfl⟩ := FiltQuot.functor_map_surjective U f
    rw [← Functor.map_smul, CategoryTheory.Quotient.lift_map_functor_map,
      CategoryTheory.Quotient.lift_map_functor_map, Functor.map_smul]

/-- The duality functor `𝒜/𝒰 → ℬ` induced by a duality functor `𝒜 → ℬ` killing the ideal of
`𝒰`, with the same `ξ`. -/
private def liftDual (F : DualFunctor A B)
    (H : ∀ (x y : A) (f₁ f₂ : x ⟶ y), FiltQuot.rel U f₁ f₂ →
      F.toFunctor.map f₁ = F.toFunctor.map f₂) : DualFunctor (FiltQuot U) B where
  toFunctor := liftFun U F.toFunctor H
  ξ M := F.ξ M.as
  ξ_natural {M N} f := by
    obtain ⟨f, rfl⟩ := FiltQuot.functor_map_surjective U f
    rw [FiltQuot.dualHom_map, CategoryTheory.Quotient.lift_map_functor_map,
      CategoryTheory.Quotient.lift_map_functor_map]
    exact F.ξ_natural f
  ξ_dual M := F.ξ_dual M.as

private theorem liftDual_isStrict (F : DualFunctor A B)
    (H : ∀ (x y : A) (f₁ f₂ : x ⟶ y), FiltQuot.rel U f₁ f₂ →
      F.toFunctor.map f₁ = F.toFunctor.map f₂) (hF : F.IsStrict) :
    (liftDual U F H).IsStrict :=
  fun M => hF M.as

private theorem liftDual_spec (F : DualFunctor A B)
    (H : ∀ (x y : A) (f₁ f₂ : x ⟶ y), FiltQuot.rel U f₁ f₂ →
      F.toFunctor.map f₁ = F.toFunctor.map f₂) :
    FiltQuot.functor U ⋙ (liftDual U F H).toFunctor = F.toFunctor :=
  CategoryTheory.Quotient.lift_spec _ _ H

end Lift

private theorem comp_isStrict' {A B C : Type*} [Category A] [Preadditive A] [Linear ℚ A]
    [HasFiniteBiproducts A] [DualCat A] [Category B] [Preadditive B] [Linear ℚ B]
    [HasFiniteBiproducts B] [DualCat B] [Category C] [Preadditive C] [Linear ℚ C]
    [HasFiniteBiproducts C] [DualCat C] {F : DualFunctor A B} {G : DualFunctor B C}
    (hF : F.IsStrict) (hG : G.IsStrict) : (F.comp G).IsStrict := fun M => by
  obtain ⟨h₁, e₁⟩ := hF M
  obtain ⟨h₂, e₂⟩ := hG (F.toFunctor.obj M)
  refine ⟨(congrArg G.toFunctor.obj h₁).trans h₂, ?_⟩
  simp only [DualFunctor.comp_ξ, Iso.trans_hom, Functor.mapIso_hom, e₁, e₂, eqToHom_map,
    eqToHom_trans]
  rfl

section Functors

variable (S Y Z : Set X)

private theorem compat₀ (x y : (supp S : ObjectProperty (AsymCat G X)).FullSubcategory)
    (f₁ f₂ : x ⟶ y) (h : FiltQuot.rel (suppIn S Z) f₁ f₂) :
    (FiltQuot.q (suppIn S (Y ∪ Z))).toFunctor.map f₁ =
      (FiltQuot.q (suppIn S (Y ∪ Z))).toFunctor.map f₂ :=
  (FiltQuot.functor_map_eq_iff _ _ _).2 (ideal_suppIn_mono Set.subset_union_right h)

/-- `𝒜_S/𝒜_Z → 𝒜_S/𝒜_{Y ∪ Z}`, `[u] ↦ [u]`. -/
private def iterQuot₀ :
    DualFunctor (FiltQuot (suppIn (G := G) S Z)) (FiltQuot (suppIn (G := G) S (Y ∪ Z))) :=
  liftDual (suppIn S Z) (FiltQuot.q _) (compat₀ S Y Z)

private theorem compat (x y : FiltQuot (suppIn (G := G) S Z)) (f₁ f₂ : x ⟶ y)
    (h : FiltQuot.rel (quotSupp S Z Y) f₁ f₂) :
    (iterQuot₀ S Y Z).toFunctor.map f₁ = (iterQuot₀ S Y Z).toFunctor.map f₂ := by
  obtain ⟨g₁, rfl⟩ := FiltQuot.functor_map_surjective (suppIn S Z) f₁
  obtain ⟨g₂, rfl⟩ := FiltQuot.functor_map_surjective (suppIn S Z) f₂
  obtain ⟨V, hV, A, B, hAB⟩ := h
  obtain ⟨a, rfl⟩ := FiltQuot.functor_map_surjective (suppIn S Z) A
  obtain ⟨b, rfl⟩ := FiltQuot.functor_map_surjective (suppIn S Z) B
  rw [← Functor.map_sub, ← Functor.map_comp, FiltQuot.functor_map_eq_iff] at hAB
  change (FiltQuot.functor (suppIn S Z) ⋙ (iterQuot₀ S Y Z).toFunctor).map g₁ =
    (FiltQuot.functor (suppIn S Z) ⋙ (iterQuot₀ S Y Z).toFunctor).map g₂
  rw [iterQuot₀, liftDual_spec]
  change (FiltQuot.functor _).map g₁ = (FiltQuot.functor _).map g₂
  rw [FiltQuot.functor_map_eq_iff]
  have he : g₁ - g₂ = (g₁ - g₂ - a ≫ b) + a ≫ b := by abel
  rw [he]
  exact FiltQuot.ideal_add (ideal_suppIn_mono Set.subset_union_right hAB)
    (ideal_suppIn_mono Set.subset_union_left ⟨V.as, hV, a, b, rfl⟩)

/-- The strict duality functor `(𝒜_S/𝒜_Z)/𝒰_Y → 𝒜_S/𝒜_{Y ∪ Z}`, `[[u]] ↦ [u]`. -/
private def iterQuotDual :
    DualFunctor (FiltQuot (quotSupp (G := G) S Z Y)) (FiltQuot (suppIn (G := G) S (Y ∪ Z))) :=
  liftDual (quotSupp S Z Y) (iterQuot₀ S Y Z) (compat S Y Z)

private theorem compatInv (x y : (supp S : ObjectProperty (AsymCat G X)).FullSubcategory)
    (f₁ f₂ : x ⟶ y) (h : FiltQuot.rel (suppIn S (Y ∪ Z)) f₁ f₂) :
    ((FiltQuot.q (suppIn S Z)).comp (FiltQuot.q (quotSupp S Z Y))).toFunctor.map f₁ =
      ((FiltQuot.q (suppIn S Z)).comp (FiltQuot.q (quotSupp S Z Y))).toFunctor.map f₂ := by
  obtain ⟨u, z, hu, hz, he⟩ := ideal_union_split h
  change (FiltQuot.functor _).map ((FiltQuot.functor (suppIn S Z)).map f₁) =
    (FiltQuot.functor _).map ((FiltQuot.functor (suppIn S Z)).map f₂)
  rw [FiltQuot.functor_map_eq_iff, ← Functor.map_sub]
  have h1 : (FiltQuot.functor (suppIn S Z)).map (f₁ - f₂) =
      (FiltQuot.functor (suppIn S Z)).map u := by
    rw [FiltQuot.functor_map_eq_iff, he, add_sub_cancel_left]
    exact hz
  rw [h1]
  obtain ⟨V, hV, a, b, rfl⟩ := hu
  exact ⟨(FiltQuot.functor _).obj V, hV, (FiltQuot.functor _).map a,
    (FiltQuot.functor _).map b, Functor.map_comp _ _ _⟩

/-- The strict duality functor `𝒜_S/𝒜_{Y ∪ Z} → (𝒜_S/𝒜_Z)/𝒰_Y`, `[u] ↦ [[u]]`. -/
private def iterQuotInvDual :
    DualFunctor (FiltQuot (suppIn (G := G) S (Y ∪ Z))) (FiltQuot (quotSupp (G := G) S Z Y)) :=
  liftDual (suppIn S (Y ∪ Z)) ((FiltQuot.q (suppIn S Z)).comp (FiltQuot.q (quotSupp S Z Y)))
    (compatInv S Y Z)

private theorem iterQuotDual_isStrict : (iterQuotDual (G := G) S Y Z).IsStrict :=
  liftDual_isStrict _ _ _ (liftDual_isStrict _ _ _ (FiltQuot.q_isStrict _))

private theorem iterQuotInvDual_isStrict : (iterQuotInvDual (G := G) S Y Z).IsStrict :=
  liftDual_isStrict _ _ _ (comp_isStrict' (FiltQuot.q_isStrict _) (FiltQuot.q_isStrict _))

private theorem spec₁ :
    (FiltQuot.functor (suppIn S Z) ⋙ FiltQuot.functor (quotSupp S Z Y)) ⋙
      (iterQuotDual (G := G) S Y Z).toFunctor = FiltQuot.functor (suppIn S (Y ∪ Z)) := by
  rw [Functor.assoc, iterQuotDual, liftDual_spec, iterQuot₀, liftDual_spec]
  rfl

private theorem spec₂ :
    FiltQuot.functor (suppIn S (Y ∪ Z)) ⋙ (iterQuotInvDual (G := G) S Y Z).toFunctor =
      FiltQuot.functor (suppIn S Z) ⋙ FiltQuot.functor (quotSupp S Z Y) := by
  rw [iterQuotInvDual, liftDual_spec]
  rfl

private theorem comp₁ :
    (iterQuotDual (G := G) S Y Z).toFunctor ⋙ (iterQuotInvDual S Y Z).toFunctor =
      𝟭 (FiltQuot (quotSupp S Z Y)) := by
  refine CategoryTheory.Quotient.lift_unique' (FiltQuot.rel (quotSupp S Z Y)) _ _ ?_
  refine CategoryTheory.Quotient.lift_unique' (FiltQuot.rel (suppIn S Z)) _ _ ?_
  rw [Functor.comp_id, ← Functor.assoc, ← Functor.assoc, spec₁, spec₂]

private theorem comp₂ :
    (iterQuotInvDual (G := G) S Y Z).toFunctor ⋙ (iterQuotDual S Y Z).toFunctor =
      𝟭 (FiltQuot (suppIn S (Y ∪ Z))) := by
  refine CategoryTheory.Quotient.lift_unique' (FiltQuot.rel (suppIn S (Y ∪ Z))) _ _ ?_
  rw [Functor.comp_id, ← Functor.assoc, spec₂, spec₁]

end Functors

/-- **Iterated quotient.** The identity on objects and on representatives gives mutually inverse
strict duality functors `(𝒜_S/𝒜_Z)/𝒰_Y ≅ 𝒜_S/𝒜_{Y ∪ Z}` that commute with the quotient functors
from `𝒜_S`. -/
def iteratedQuotient (S Y Z : Set X) :
    {e : DualFunctor (FiltQuot (quotSupp (G := G) S Z Y)) (FiltQuot (suppIn (G := G) S (Y ∪ Z))) ×
        DualFunctor (FiltQuot (suppIn (G := G) S (Y ∪ Z))) (FiltQuot (quotSupp (G := G) S Z Y)) //
      e.1.IsStrict ∧ e.2.IsStrict ∧ e.1.toFunctor ⋙ e.2.toFunctor = 𝟭 _ ∧
        e.2.toFunctor ⋙ e.1.toFunctor = 𝟭 _ ∧
        (FiltQuot.functor (suppIn S Z) ⋙ FiltQuot.functor (quotSupp S Z Y)) ⋙ e.1.toFunctor =
          FiltQuot.functor (suppIn S (Y ∪ Z)) ∧
        FiltQuot.functor (suppIn S (Y ∪ Z)) ⋙ e.2.toFunctor =
          FiltQuot.functor (suppIn S Z) ⋙ FiltQuot.functor (quotSupp S Z Y)} :=
  ⟨(iterQuotDual S Y Z, iterQuotInvDual S Y Z), iterQuotDual_isStrict S Y Z,
    iterQuotInvDual_isStrict S Y Z, comp₁ S Y Z, comp₂ S Y Z, spec₁ S Y Z, spec₂ S Y Z⟩

end HSP
