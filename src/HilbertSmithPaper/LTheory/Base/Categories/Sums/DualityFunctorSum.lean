import HilbertSmithPaper.LTheory.Base.Categories.Sums.DualBinaryBiproducts
import HilbertSmithPaper.LTheory.Base.Categories.DualityFunctor
import HilbertSmithPaper.LTheory.Base.Categories.Sums.DualBiproduct

/-!
# Sum of duality functors

For duality functors `(F, ξ), (G, ζ) : B → B'`, the sum `F ⊕ G` is the functor
`M ↦ F M ⊕ G M`, `f ↦ F f ⊕ G f`, with duality isomorphism `ξ ⊕ ζ` followed by the canonical
isomorphism `F M^* ⊕ G M^* ≅ (F M ⊕ G M)^*` (`HSP.DualFunctor.biprod`).
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v₁ v₂ u₁ u₂

variable {B : Type u₁} [Category.{v₁} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]
  {B' : Type u₂} [Category.{v₂} B'] [Preadditive B'] [Linear ℚ B'] [HasFiniteBiproducts B']
  [DualCat B']

namespace DualFunctor

variable (F G : DualFunctor B B')

/-- The underlying functor `M ↦ F M ⊕ G M`. -/
@[simps]
private noncomputable def biprodFunctor : B ⥤ B' where
  obj M := F.toFunctor.obj M ⊞ G.toFunctor.obj M
  map f := biprod.map (F.toFunctor.map f) (G.toFunctor.map f)
  map_id M := by
    show biprod.map (F.toFunctor.map (𝟙 M)) (G.toFunctor.map (𝟙 M)) =
      𝟙 (F.toFunctor.obj M ⊞ G.toFunctor.obj M)
    rw [F.toFunctor.map_id, G.toFunctor.map_id]
    apply biprod.hom_ext <;> simp
  map_comp f g := by
    apply biprod.hom_ext <;> simp

private instance : (biprodFunctor F G).Additive where
  map_add {M N f g} := by
    show biprod.map (F.toFunctor.map (f + g)) (G.toFunctor.map (f + g)) =
      biprod.map (F.toFunctor.map f) (G.toFunctor.map f) +
        biprod.map (F.toFunctor.map g) (G.toFunctor.map g)
    rw [F.toFunctor.map_add, G.toFunctor.map_add]
    apply biprod.hom_ext <;> simp [Preadditive.add_comp]

private instance : (biprodFunctor F G).Linear ℚ where
  map_smul {M N} f c := by
    show biprod.map (F.toFunctor.map (c • f)) (G.toFunctor.map (c • f)) =
      c • biprod.map (F.toFunctor.map f) (G.toFunctor.map f)
    rw [Functor.Linear.map_smul, Functor.Linear.map_smul]
    apply biprod.hom_ext <;> simp [Linear.smul_comp]

omit [Linear ℚ B'] [DualCat B'] in
private lemma eqToHom_fst' {P X Y X' Y' Z W : B'} (k : X' ⟶ W) (hP : P = (X ⊞ Y))
    (h : P = (X' ⊞ Y')) (hX : X = X') (hY : Y = Y') (e₁ : X = Z) (e₂ : Z = X') :
    (eqToHom hP ≫ biprod.fst ≫ eqToHom e₁) ≫ eqToHom e₂ ≫ k = eqToHom h ≫ biprod.fst ≫ k := by
  subst hP hX hY e₁
  simp

omit [Linear ℚ B'] [DualCat B'] in
private lemma eqToHom_snd' {P X Y X' Y' Z W : B'} (k : Y' ⟶ W) (hP : P = (X ⊞ Y))
    (h : P = (X' ⊞ Y')) (hX : X = X') (hY : Y = Y') (e₁ : Y = Z) (e₂ : Z = Y') :
    (eqToHom hP ≫ biprod.snd ≫ eqToHom e₁) ≫ eqToHom e₂ ≫ k = eqToHom h ≫ biprod.snd ≫ k := by
  subst hP hX hY e₁
  simp

private lemma desc_dualHom_inl (M N : B') :
    biprod.desc (dualHom biprod.fst) (dualHom biprod.snd) ≫ dualHom (biprod.inl : M ⟶ M ⊞ N) =
      biprod.fst :=
  dualBiprodIso_inv_dualHom_inl M N

private lemma desc_dualHom_inr (M N : B') :
    biprod.desc (dualHom biprod.fst) (dualHom biprod.snd) ≫ dualHom (biprod.inr : N ⟶ M ⊞ N) =
      biprod.snd :=
  dualBiprodIso_inv_dualHom_inr M N

/-- **The sum of duality functors** `F ⊕ G`: `M ↦ F M ⊕ G M`, with duality isomorphism `ξ ⊕ ζ`
followed by the canonical isomorphism `F M^* ⊕ G M^* ≅ (F M ⊕ G M)^*`. -/
noncomputable def biprod : DualFunctor B B' where
  toFunctor := biprodFunctor F G
  ξ M := biprod.mapIso (F.ξ M) (G.ξ M) ≪≫ (dualBiprodIso _ _).symm
  ξ_natural {M N} f := by
    change biprod.map (F.toFunctor.map (dualHom f)) (G.toFunctor.map (dualHom f)) ≫
        biprod.map (F.ξ M).hom (G.ξ M).hom ≫ biprod.desc (dualHom biprod.fst) (dualHom biprod.snd) =
      (biprod.map (F.ξ N).hom (G.ξ N).hom ≫ biprod.desc (dualHom biprod.fst) (dualHom biprod.snd)) ≫
        dualHom (biprod.map (F.toFunctor.map f) (G.toFunctor.map f))
    apply biprod.hom_ext'
    · simp only [biprod.inl_map_assoc, biprod.inl_desc_assoc, Category.assoc, ← dualHom_comp,
        biprod.map_fst]
      rw [← Category.assoc, F.ξ_natural, Category.assoc, biprod.inl_desc, dualHom_comp]
    · simp only [biprod.inr_map_assoc, biprod.inr_desc_assoc, Category.assoc, ← dualHom_comp,
        biprod.map_snd]
      rw [← Category.assoc, G.ξ_natural, Category.assoc, biprod.inr_desc, dualHom_comp]
  ξ_dual M := by
    change dualHom (biprod.map (F.ξ M).hom (G.ξ M).hom ≫
        biprod.desc (dualHom biprod.fst) (dualHom biprod.snd)) =
      eqToHom (show dual (dual (F.toFunctor.obj M ⊞ G.toFunctor.obj M)) =
        (F.toFunctor.obj (dual (dual M)) ⊞ G.toFunctor.obj (dual (dual M))) by
          rw [dual_dual, dual_dual]) ≫
      (biprod.map (F.ξ (dual M)).hom (G.ξ (dual M)).hom ≫
        biprod.desc (dualHom biprod.fst) (dualHom biprod.snd))
    rw [← cancel_mono (dualBiprodIso (F.toFunctor.obj (dual M)) (G.toFunctor.obj (dual M))).hom]
    apply biprod.hom_ext
    · simp only [dualBiprodIso, Category.assoc, biprod.lift_fst, ← dualHom_comp,
        biprod.inl_map_assoc, biprod.inl_desc, desc_dualHom_inl]
      rw [dualHom_comp, dualHom_dualHom, F.ξ_dual, biprod.map_fst]
      exact eqToHom_fst' _ _ _ (congrArg F.toFunctor.obj (dual_dual M)).symm
        (congrArg G.toFunctor.obj (dual_dual M)).symm _ _
    · simp only [dualBiprodIso, Category.assoc, biprod.lift_snd, ← dualHom_comp,
        biprod.inr_map_assoc, biprod.inr_desc, desc_dualHom_inr]
      rw [dualHom_comp, dualHom_dualHom, G.ξ_dual, biprod.map_snd]
      exact eqToHom_snd' _ _ _ (congrArg F.toFunctor.obj (dual_dual M)).symm
        (congrArg G.toFunctor.obj (dual_dual M)).symm _ _

private lemma biprod_obj (M : B) :
    (F.biprod G).toFunctor.obj M = (F.toFunctor.obj M ⊞ G.toFunctor.obj M) :=
  rfl

lemma biprod_map {M N : B} (f : M ⟶ N) :
    (F.biprod G).toFunctor.map f = biprod.map (F.toFunctor.map f) (G.toFunctor.map f) :=
  rfl

private lemma biprod_ξ_hom (M : B) :
    ((F.biprod G).ξ M).hom = biprod.map (F.ξ M).hom (G.ξ M).hom ≫
      (dualBiprodIso (F.toFunctor.obj M) (G.toFunctor.obj M)).inv :=
  rfl

/-- The duality isomorphism of `F ⊕ G`, between maps into the summands: for
`f, g` into `F(M^*), G(M^*)` and `a, b` into `F M, G M`,
`(a, b)^* ∘ ξ^{F ⊕ G}_M ∘ (f, g) = a^* ξ_M f + b^* ζ_M g`. -/
lemma lift_biprod_ξ_dualHom_lift {X Y : B'} (M : B) (f : X ⟶ F.toFunctor.obj (dual M))
    (g : X ⟶ G.toFunctor.obj (dual M)) (a : Y ⟶ F.toFunctor.obj M) (b : Y ⟶ G.toFunctor.obj M) :
    biprod.lift f g ≫ ((F.biprod G).ξ M).hom ≫ dualHom (biprod.lift a b) =
      f ≫ (F.ξ M).hom ≫ dualHom a + g ≫ (G.ξ M).hom ≫ dualHom b := by
  have h : (dualBiprodIso (F.toFunctor.obj M) (G.toFunctor.obj M)).inv ≫
      dualHom (biprod.lift a b) = biprod.desc (dualHom a) (dualHom b) := by
    apply biprod.hom_ext'
    · rw [dualBiprodIso, biprod.inl_desc_assoc, ← dualHom_comp, biprod.lift_fst,
        biprod.inl_desc]
    · rw [dualBiprodIso, biprod.inr_desc_assoc, ← dualHom_comp, biprod.lift_snd,
        biprod.inr_desc]
  rw [biprod_ξ_hom]
  erw [Category.assoc, h]
  have h' : Limits.biprod.map (F.ξ M).hom (G.ξ M).hom ≫ Limits.biprod.desc (dualHom a) (dualHom b) =
      Limits.biprod.desc ((F.ξ M).hom ≫ dualHom a) ((G.ξ M).hom ≫ dualHom b) := by
    apply Limits.biprod.hom_ext' <;> simp
  rw [h', Limits.biprod.lift_desc]

end DualFunctor

end HSP
