import HilbertSmithPaper.Categories.Supports.SupportIdeal
import HilbertSmithPaper.Categories.Supports.ThickeningInvariant
import HilbertSmithPaper.Categories.Supports.RelativeIntersectionAdditive
import HilbertSmithPaper.Categories.Supports.NullThickening
import HilbertSmithPaper.Categories.Asymptotic.Restriction.InclusionProjection
import HilbertSmithPaper.Categories.Asymptotic.Restriction.ProjectionInclusion
import HilbertSmithPaper.Categories.Asymptotic.Restriction.DiagonalProjectionComplement
import HilbertSmithPaper.Categories.Asymptotic.Restriction.DiagonalProjectionColumns
import HilbertSmithPaper.LTheory.Ultimate.Boundary.ExcisivePair
import HilbertSmithPaper.Categories.Asymptotic.Structure.TransposeTranspose

/-!
# Excision equivalence

Let the action be isometric, `A, B ⊆ X` with `B` invariant, and `S = A ∪ B`. In `𝒜_S`, let
`𝒰_A = suppIn S A`, `𝒰_B = suppIn S B` and `𝒰_A ∩ 𝒰_B` the `B`-supported objects of `𝒰_A`
(`ExcisivePair.inter`); `𝒰_A/(𝒰_A ∩ 𝒰_B)` realizes `𝒜_A/𝒜_{A∩B}`. The excision equivalence
`e : 𝒰_A/(𝒰_A ∩ 𝒰_B) → 𝒜_S/𝒜_B` is the strict duality functor induced by inclusion
(`ExcisivePair.e`). `HSP.excision` gives its inverse `R` with unitary unit `id ≅ R ∘ e` and counit
`e ∘ R ≅ id`.

For `M ∈ 𝒜_S` a null sequence `a` is chosen (classically) with the labels of `M` eventually in
`N̄_{a_i}(S)`; `M_A` (`HSP.exObj`) keeps the indices with labels in `N̄_{a_i}(A)`, and `ι, π` are its
coordinate inclusion and projection. The complement `M_far` is `B`-supported and, when `M` is
`A`-supported, `A`-supported. `R(M) = M_A` and `R[u] = [ι u π]` (diagrammatic order). It is well
defined and functorial by `HSP.ideal_inter_of_ideal_supp`: a map between objects of `𝒰_A` that
factors through a `B`-supported object of `𝒜_S` factors through an object of `𝒰_A ∩ 𝒰_B` (restrict
its source to its nonzero columns, whose labels are near `B` by the support ideal). The unit and
counit have components `[π]` and `[ι]`, with inverses their transposes.
-/

open CategoryTheory CategoryTheory.Limits Filter Metric Topology
open scoped NNReal

namespace HSP

open DualCat

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

/-- The indices `k` with `x_i(k)` in the closed `r_i`-thickening of `A`. -/
private def nearIdx (A : Set X) (M : AsymPre G X) (r : ℕ → ℝ≥0) : ∀ i, Fin (M.n i) → Prop :=
  fun i k => M.x i k ∈ cthickening (r i) A

private theorem supp_restrict {S : Set X} {M : AsymPre G X} (hM : supp S (⟨M⟩ : AsymCat G X))
    (P : ∀ i, Fin (M.n i) → Prop) : supp S (⟨M.restrict P⟩ : AsymCat G X) := fun ε hε =>
  (hM ε hε).mono fun _ h _ => h _

private theorem supp_restrict_near {A : Set X} {M : AsymPre G X} {r : ℕ → ℝ≥0}
    (hr : Tendsto r atTop (𝓝 0)) : supp A (⟨M.restrict (nearIdx A M r)⟩ : AsymCat G X) := by
  intro ε hε
  filter_upwards [(NNReal.tendsto_coe.2 hr).eventually (gt_mem_nhds hε)] with i hi k
  exact cthickening_subset_thickening' hε hi A (AsymPre.restrictEmb_mem k)

variable [IsIsometricVAdd (ZMod p) X]

/-- **Key lemma.** A map between objects of `𝒰_A` that factors in `𝒜_S` through a `B`-supported
object (`B` invariant) factors through an object of `𝒰_A ∩ 𝒰_B`. -/
private theorem ideal_inter_of_ideal_supp {S A B : Set X} (hB : ∀ c : ZMod p, ∀ x ∈ B, c +ᵥ x ∈ B)
    {V W : (suppIn (G := G) S A).FullSubcategory} (f : V ⟶ W)
    (hf : FiltQuot.ideal (suppIn S B) f.hom) :
    FiltQuot.ideal (ExcisivePair.inter (suppIn S A) (suppIn S B)) f := by
  classical
  obtain ⟨U, hU, a, b, hab⟩ := hf
  obtain ⟨u, hu⟩ := AsymCat.mkHom_surjective f.hom.hom
  have hI : FiltQuot.ideal (supp B) (AsymCat.mkHom u) :=
    ⟨U.obj, hU, a.hom, b.hom, by rw [hu, hab]; rfl⟩
  have h := (factorsThrough_supp_iff hB u).1 hI
  let Q : ∀ i, Fin (V.obj.obj.as.n i) → Prop := fun i k =>
    ∃ (g : G.G i) (c : G.G i × Fin (W.obj.obj.as.n i)),
      FreeCat.mat (AsymPre.coord u i) c (g, k) ≠ 0
  let V' : (suppIn (G := G) S A).FullSubcategory :=
    ⟨⟨⟨V.obj.obj.as.restrict Q⟩, supp_restrict V.obj.property _⟩, supp_restrict V.property _⟩
  refine ⟨V', fun ε hε => ?_, ObjectProperty.homMk (ObjectProperty.homMk
    (AsymCat.mkHom (AsymPre.restrictPro _ _))), ObjectProperty.homMk (ObjectProperty.homMk
    (AsymCat.mkHom (AsymPre.restrictInc _ _ ≫ u))), ?_⟩
  · filter_upwards [h ε hε] with i hi k
    obtain ⟨g, c, hgc⟩ := AsymPre.restrictEmb_mem (P := Q) k
    exact (vadd_mem_thickening_iff hB _).1 (hi c _ hgc).2
  · refine ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _ ?_)
    change f.hom.hom = AsymCat.mkHom _ ≫ AsymCat.mkHom _
    rw [← hu, ← Functor.map_comp, ← Category.assoc, AsymPre.restrictPro_restrictInc,
      AsymPre.trunc_comp_eq]
    exact fun i c b hcb => ⟨b.1, c, hcb⟩

section Excision

variable (S A B : Set X)

/-- The chosen null sequence for `M ∈ 𝒜_{A∪B}`: eventually all labels of `M` lie in its closed
thickenings of `A ∪ B`. -/
private noncomputable def exNull (M : (supp S : ObjectProperty (AsymCat G X)).FullSubcategory) :
    ℕ → ℝ≥0 :=
  Classical.choose (exists_null_cthickening (M := M.obj.as) S (fun _ _ => True)
    (fun ε hε => (M.property ε hε).mono fun _ hi k _ => hi k))

omit [IsIsometricVAdd (ZMod p) X] in
private theorem exNull_spec (M : (supp S : ObjectProperty (AsymCat G X)).FullSubcategory) :
    Tendsto (exNull S M) atTop (𝓝 0) ∧
      ∀ᶠ i in atTop, ∀ k, True → M.obj.as.x i k ∈ cthickening (exNull S M i) S :=
  Classical.choose_spec (exists_null_cthickening (M := M.obj.as) S (fun _ _ => True)
    (fun ε hε => (M.property ε hε).mono fun _ hi k _ => hi k))

/-- The indices of `M` with labels in `N̄_{a_i}(A)`. -/
private def exIdx (M : (supp S : ObjectProperty (AsymCat G X)).FullSubcategory) :
    ∀ i, Fin (M.obj.as.n i) → Prop :=
  nearIdx A M.obj.as (exNull S M)

/-- `M_A`, an object of `𝒰_A`. -/
private noncomputable def exObj (M : (supp S : ObjectProperty (AsymCat G X)).FullSubcategory) :
    (suppIn (G := G) S A).FullSubcategory :=
  ⟨⟨⟨M.obj.as.restrict (exIdx S A M)⟩, supp_restrict M.property _⟩,
    supp_restrict_near (exNull_spec S M).1⟩

/-- `M_far`, the complement of `M_A`. -/
private noncomputable def exFar (M : (supp S : ObjectProperty (AsymCat G X)).FullSubcategory) :
    (supp S : ObjectProperty (AsymCat G X)).FullSubcategory :=
  ⟨⟨M.obj.as.restrict (fun i k => ¬exIdx S A M i k)⟩, supp_restrict M.property _⟩

omit [IsIsometricVAdd (ZMod p) X] in
private theorem supp_exFar (hS : S ⊆ A ∪ B) (M : (supp S : ObjectProperty (AsymCat G X)).FullSubcategory) :
    supp B (exFar S A M).obj := by
  intro ε hε
  filter_upwards [(exNull_spec S M).2,
    (NNReal.tendsto_coe.2 (exNull_spec S M).1).eventually (gt_mem_nhds hε)] with i hi hri k
  have hk := AsymPre.restrictEmb_mem (P := fun i k => ¬exIdx S A M i k) k
  have h := cthickening_subset_of_subset _ hS
    (hi (M.obj.as.restrictEmb (fun i k => ¬exIdx S A M i k) i k) trivial)
  rw [cthickening_union] at h
  exact cthickening_subset_thickening' hε hri B (h.resolve_left hk)

/-- The coordinate inclusion `ι : M_A → M`. -/
private noncomputable def exInc (M : (supp S : ObjectProperty (AsymCat G X)).FullSubcategory) :
    (exObj S A M).obj ⟶ M :=
  ObjectProperty.homMk (AsymCat.mkHom (AsymPre.restrictInc _ _))

/-- The coordinate projection `π : M → M_A`. -/
private noncomputable def exPro (M : (supp S : ObjectProperty (AsymCat G X)).FullSubcategory) :
    M ⟶ (exObj S A M).obj :=
  ObjectProperty.homMk (AsymCat.mkHom (AsymPre.restrictPro _ _))

/-- The coordinate inclusion of `M_far`. -/
private noncomputable def exFarInc (M : (supp S : ObjectProperty (AsymCat G X)).FullSubcategory) :
    exFar S A M ⟶ M :=
  ObjectProperty.homMk (AsymCat.mkHom (AsymPre.restrictInc _ _))

/-- The coordinate projection onto `M_far`. -/
private noncomputable def exFarPro (M : (supp S : ObjectProperty (AsymCat G X)).FullSubcategory) :
    M ⟶ exFar S A M :=
  ObjectProperty.homMk (AsymCat.mkHom (AsymPre.restrictPro _ _))

omit [IsIsometricVAdd (ZMod p) X] in
private theorem exInc_exPro (M : (supp S : ObjectProperty (AsymCat G X)).FullSubcategory) :
    exInc S A M ≫ exPro S A M = 𝟙 _ := by
  refine ObjectProperty.hom_ext _ ?_
  change AsymCat.mkHom _ ≫ AsymCat.mkHom _ = 𝟙 _
  rw [← Functor.map_comp, AsymPre.restrictInc_restrictPro, CategoryTheory.Functor.map_id]
  rfl

omit [IsIsometricVAdd (ZMod p) X] in
private theorem one_sub_exPro_exInc (M : (supp S : ObjectProperty (AsymCat G X)).FullSubcategory) :
    𝟙 M - exPro S A M ≫ exInc S A M = exFarPro S A M ≫ exFarInc S A M := by
  classical
  refine ObjectProperty.hom_ext _ ?_
  change 𝟙 M.obj - AsymCat.mkHom _ ≫ AsymCat.mkHom _ = AsymCat.mkHom _ ≫ AsymCat.mkHom _
  rw [← Functor.map_comp, ← Functor.map_comp, AsymPre.restrictPro_restrictInc,
    AsymPre.restrictPro_restrictInc, AsymPre.trunc_not, Functor.map_sub,
    CategoryTheory.Functor.map_id]
  rfl

omit [IsIsometricVAdd (ZMod p) X] in
private theorem dualHom_exInc (M : (supp S : ObjectProperty (AsymCat G X)).FullSubcategory) :
    dualHom (exInc S A M) = exPro S A M := rfl

omit [IsIsometricVAdd (ZMod p) X] in
private theorem dualHom_exPro (M : (supp S : ObjectProperty (AsymCat G X)).FullSubcategory) :
    dualHom (exPro S A M) = exInc S A M := by
  refine ObjectProperty.hom_ext _ ?_
  exact congrArg AsymCat.mkHom (AsymPre.transpose_transpose _)

omit [IsIsometricVAdd (ZMod p) X] in
/-- `𝟙 - πι` lies in the ideal of `𝒜_B`. -/
private theorem ideal_one_sub (hS : S ⊆ A ∪ B) (M : (supp S : ObjectProperty (AsymCat G X)).FullSubcategory) :
    FiltQuot.ideal (suppIn S B) (𝟙 M - exPro S A M ≫ exInc S A M) := by
  rw [one_sub_exPro_exInc]
  exact ⟨_, supp_exFar S A B hS M, _, _, rfl⟩

/-- The map `ι u π : M_A → N_A` of `𝒰_A`. -/
private noncomputable def exMap {M N : (supp S : ObjectProperty (AsymCat G X)).FullSubcategory}
    (u : M ⟶ N) : exObj S A M ⟶ exObj S A N :=
  ObjectProperty.homMk (exInc S A M ≫ u ≫ exPro S A N)

variable {S A B}

private theorem exMap_ideal (hB : ∀ c : ZMod p, ∀ x ∈ B, c +ᵥ x ∈ B)
    {M N : (supp S : ObjectProperty (AsymCat G X)).FullSubcategory} {u : M ⟶ N}
    (hu : FiltQuot.ideal (suppIn S B) u) :
    FiltQuot.ideal (ExcisivePair.inter (suppIn S A) (suppIn S B)) (exMap S A u) :=
  ideal_inter_of_ideal_supp hB _
    (FiltQuot.ideal_comp_left _ (FiltQuot.ideal_comp_right hu _))

variable (S A B)

/-- `R₀ : 𝒜_S → 𝒰_A/(𝒰_A ∩ 𝒰_B)`, `M ↦ M_A`, `u ↦ [ι u π]`. -/
private noncomputable def exFunctor₀ (hS : S ⊆ A ∪ B) (hB : ∀ c : ZMod p, ∀ x ∈ B, c +ᵥ x ∈ B) :
    (supp S : ObjectProperty (AsymCat G X)).FullSubcategory ⥤
      FiltQuot (ExcisivePair.inter (suppIn (G := G) S A) (suppIn S B)) where
  obj M := (FiltQuot.functor _).obj (exObj S A M)
  map u := (FiltQuot.functor _).map (exMap S A u)
  map_id M := by
    rw [← CategoryTheory.Functor.map_id]
    congr 1
    refine ObjectProperty.hom_ext _ ?_
    change exInc S A M ≫ 𝟙 M ≫ exPro S A M = 𝟙 _
    rw [Category.id_comp, exInc_exPro]
  map_comp {M N L} u v := by
    rw [← Functor.map_comp, FiltQuot.functor_map_eq_iff]
    have he : exMap S A (u ≫ v) - exMap S A u ≫ exMap S A v =
        exMap S A (u ≫ (𝟙 N - exPro S A N ≫ exInc S A N) ≫ v) := by
      refine ObjectProperty.hom_ext _ ?_
      change exInc S A M ≫ (u ≫ v) ≫ exPro S A L -
          (exInc S A M ≫ u ≫ exPro S A N) ≫ exInc S A N ≫ v ≫ exPro S A L =
        exInc S A M ≫ (u ≫ (𝟙 N - exPro S A N ≫ exInc S A N) ≫ v) ≫ exPro S A L
      simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.assoc, Category.id_comp]
    rw [he]
    exact exMap_ideal hB (FiltQuot.ideal_comp_left _ (FiltQuot.ideal_comp_right
      (ideal_one_sub S A B hS N) _))

omit [IsIsometricVAdd (ZMod p) X] in
private theorem exMap_sub {M N : (supp S : ObjectProperty (AsymCat G X)).FullSubcategory}
    (u v : M ⟶ N) : exMap S A (u - v) = exMap S A u - exMap S A v := by
  refine ObjectProperty.hom_ext _ ?_
  change exInc S A M ≫ (u - v) ≫ exPro S A N =
    exInc S A M ≫ u ≫ exPro S A N - exInc S A M ≫ v ≫ exPro S A N
  simp only [Preadditive.sub_comp, Preadditive.comp_sub]

omit [IsIsometricVAdd (ZMod p) X] in
private theorem exMap_add {M N : (supp S : ObjectProperty (AsymCat G X)).FullSubcategory}
    (u v : M ⟶ N) : exMap S A (u + v) = exMap S A u + exMap S A v := by
  refine ObjectProperty.hom_ext _ ?_
  change exInc S A M ≫ (u + v) ≫ exPro S A N =
    exInc S A M ≫ u ≫ exPro S A N + exInc S A M ≫ v ≫ exPro S A N
  simp only [Preadditive.add_comp, Preadditive.comp_add]

omit [IsIsometricVAdd (ZMod p) X] in
private theorem exMap_smul {M N : (supp S : ObjectProperty (AsymCat G X)).FullSubcategory}
    (c : ℚ) (u : M ⟶ N) : exMap S A (c • u) = c • exMap S A u := by
  refine ObjectProperty.hom_ext _ ?_
  change exInc S A M ≫ (c • u) ≫ exPro S A N = c • (exInc S A M ≫ u ≫ exPro S A N)
  simp only [Linear.smul_comp, Linear.comp_smul]

private theorem exCompat (hS : S ⊆ A ∪ B) (hB : ∀ c : ZMod p, ∀ x ∈ B, c +ᵥ x ∈ B)
    (x y : (supp S : ObjectProperty (AsymCat G X)).FullSubcategory) (f₁ f₂ : x ⟶ y)
    (h : FiltQuot.rel (suppIn S B) f₁ f₂) :
    (exFunctor₀ S A B hS hB).map f₁ = (exFunctor₀ S A B hS hB).map f₂ := by
  change (FiltQuot.functor _).map (exMap S A f₁) = (FiltQuot.functor _).map (exMap S A f₂)
  rw [FiltQuot.functor_map_eq_iff, ← exMap_sub]
  exact exMap_ideal hB h

/-- The underlying functor of `R : 𝒜_S/𝒜_B → 𝒰_A/(𝒰_A ∩ 𝒰_B)`. -/
private noncomputable abbrev exRFunctor (hS : S ⊆ A ∪ B) (hB : ∀ c : ZMod p, ∀ x ∈ B, c +ᵥ x ∈ B) :
    FiltQuot (suppIn (G := G) S B) ⥤
      FiltQuot (ExcisivePair.inter (suppIn (G := G) S A) (suppIn S B)) :=
  CategoryTheory.Quotient.lift _ (exFunctor₀ S A B hS hB) (exCompat S A B hS hB)

private theorem exRFunctor_map (hS : S ⊆ A ∪ B) (hB : ∀ c : ZMod p, ∀ x ∈ B, c +ᵥ x ∈ B)
    {M N : (supp S : ObjectProperty (AsymCat G X)).FullSubcategory} (u : M ⟶ N) :
    (exRFunctor S A B hS hB).map ((FiltQuot.functor _).map u) =
      (FiltQuot.functor _).map (exMap S A u) :=
  CategoryTheory.Quotient.lift_map_functor_map _ _ _ _

instance (hS : S ⊆ A ∪ B) (hB : ∀ c : ZMod p, ∀ x ∈ B, c +ᵥ x ∈ B) :
    (exRFunctor (G := G) S A B hS hB).Additive where
  map_add {_ _ f g} := by
    obtain ⟨f, rfl⟩ := FiltQuot.functor_map_surjective (suppIn S B) f
    obtain ⟨g, rfl⟩ := FiltQuot.functor_map_surjective (suppIn S B) g
    rw [← Functor.map_add, exRFunctor_map S A B hS hB, exRFunctor_map S A B hS hB,
      exRFunctor_map S A B hS hB, exMap_add, Functor.map_add]
    rfl

instance (hS : S ⊆ A ∪ B) (hB : ∀ c : ZMod p, ∀ x ∈ B, c +ᵥ x ∈ B) :
    (exRFunctor (G := G) S A B hS hB).Linear ℚ where
  map_smul {_ _} f c := by
    obtain ⟨f, rfl⟩ := FiltQuot.functor_map_surjective (suppIn S B) f
    rw [← Functor.map_smul, exRFunctor_map S A B hS hB, exRFunctor_map S A B hS hB, exMap_smul,
      Functor.map_smul]
    rfl

/-- The duality functor `R : 𝒜_S/𝒜_B → 𝒰_A/(𝒰_A ∩ 𝒰_B)`, `M ↦ M_A`, `[u] ↦ [ι u π]`
(strict). -/
private noncomputable def exR (hS : S ⊆ A ∪ B) (hB : ∀ c : ZMod p, ∀ x ∈ B, c +ᵥ x ∈ B) :
    DualFunctor (FiltQuot (suppIn (G := G) S B))
      (FiltQuot (ExcisivePair.inter (suppIn (G := G) S A) (suppIn S B))) where
  toFunctor := exRFunctor S A B hS hB
  ξ M := Iso.refl _
  ξ_natural {M N} f := by
    obtain ⟨u, rfl⟩ := FiltQuot.functor_map_surjective (suppIn S B) f
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rw [FiltQuot.dualHom_map, exRFunctor_map S A B hS hB, exRFunctor_map S A B hS hB]
    refine Eq.trans ?_ (FiltQuot.dualHom_map _ (exMap S A u)).symm
    congr 1
    refine ObjectProperty.hom_ext _ ?_
    change exInc S A N.as ≫ dualHom u ≫ exPro S A M.as =
      dualHom (exInc S A M.as ≫ u ≫ exPro S A N.as)
    rw [dualHom_comp, dualHom_comp, dualHom_exInc, dualHom_exPro, Category.assoc]
  ξ_dual M := by
    simp only [Iso.refl_hom, dualHom_id, eqToHom_refl, Category.comp_id]
    rfl

omit [IsIsometricVAdd (ZMod p) X] in
private theorem unit_hom_inv (hS : S ⊆ A ∪ B) (M : FiltQuot (ExcisivePair.inter
      (suppIn (G := G) S A) (suppIn S B))) :
    (FiltQuot.functor (ExcisivePair.inter (suppIn (G := G) S A) (suppIn S B))).map (ObjectProperty.homMk (exPro S A M.as.obj) : M.as ⟶ exObj S A M.as.obj) ≫
      (FiltQuot.functor (ExcisivePair.inter (suppIn (G := G) S A) (suppIn S B))).map (ObjectProperty.homMk (exInc S A M.as.obj) : exObj S A M.as.obj ⟶ M.as) =
        𝟙 M := by
  have h1 : (FiltQuot.functor (ExcisivePair.inter (suppIn (G := G) S A) (suppIn S B))).map (𝟙 M.as) = 𝟙 M := CategoryTheory.Functor.map_id _ _
  rw [← Functor.map_comp, ← h1, FiltQuot.functor_map_eq_iff]
  have he : (ObjectProperty.homMk (exPro S A M.as.obj) : M.as ⟶ exObj S A M.as.obj) ≫
      ObjectProperty.homMk (exInc S A M.as.obj) - 𝟙 M.as =
      -((ObjectProperty.homMk (exFarPro S A M.as.obj) :
          M.as ⟶ ⟨exFar S A M.as.obj, supp_restrict M.as.property _⟩) ≫
        ObjectProperty.homMk (exFarInc S A M.as.obj)) := by
    refine ObjectProperty.hom_ext _ ?_
    change exPro S A M.as.obj ≫ exInc S A M.as.obj - 𝟙 M.as.obj =
      -(exFarPro S A M.as.obj ≫ exFarInc S A M.as.obj)
    rw [← one_sub_exPro_exInc, neg_sub]
  rw [he]
  exact FiltQuot.ideal_neg ⟨_, supp_exFar S A B hS M.as.obj, _, _, rfl⟩

omit [IsIsometricVAdd (ZMod p) X] in
private theorem unit_inv_hom (M : FiltQuot (ExcisivePair.inter (suppIn (G := G) S A)
      (suppIn S B))) :
    (FiltQuot.functor (ExcisivePair.inter (suppIn (G := G) S A) (suppIn S B))).map (ObjectProperty.homMk (exInc S A M.as.obj) : exObj S A M.as.obj ⟶ M.as) ≫
      (FiltQuot.functor (ExcisivePair.inter (suppIn (G := G) S A) (suppIn S B))).map (ObjectProperty.homMk (exPro S A M.as.obj) : M.as ⟶ exObj S A M.as.obj) =
        𝟙 ((FiltQuot.functor (ExcisivePair.inter (suppIn (G := G) S A) (suppIn S B))).obj (exObj S A M.as.obj)) := by
  rw [← Functor.map_comp, ← CategoryTheory.Functor.map_id]
  congr 1
  exact ObjectProperty.hom_ext _ (exInc_exPro S A M.as.obj)

omit [IsIsometricVAdd (ZMod p) X] in
private theorem counit_inv_hom (hS : S ⊆ A ∪ B) (M : FiltQuot (suppIn (G := G) S B)) :
    (FiltQuot.functor (suppIn S B)).map (exPro S A M.as) ≫
      (FiltQuot.functor (suppIn S B)).map (exInc S A M.as) = 𝟙 M := by
  have h1 : (FiltQuot.functor (suppIn S B)).map (𝟙 M.as) = 𝟙 M := CategoryTheory.Functor.map_id _ _
  rw [← Functor.map_comp, ← h1, FiltQuot.functor_map_eq_iff, ← neg_sub]
  exact FiltQuot.ideal_neg (ideal_one_sub S A B hS M.as)

omit [IsIsometricVAdd (ZMod p) X] in
private theorem counit_hom_inv (M : FiltQuot (suppIn (G := G) S B)) :
    (FiltQuot.functor (suppIn S B)).map (exInc S A M.as) ≫
      (FiltQuot.functor (suppIn S B)).map (exPro S A M.as) =
        𝟙 ((FiltQuot.functor (suppIn S B)).obj (exObj S A M.as).obj) := by
  rw [← Functor.map_comp, exInc_exPro, CategoryTheory.Functor.map_id]

/-- **Excision equivalence.** For an isometric action and an invariant `B`, the strict duality
functor `e : 𝒰_A/(𝒰_A ∩ 𝒰_B) → 𝒜_{A∪B}/𝒜_B` induced by inclusion has the inverse
`R(M) = M_A`, `R[u] = [ι u π]`, with a unitary unit `id ≅ R ∘ e` (components `[π]`) and a unitary
counit `e ∘ R ≅ id` (components `[ι]`). -/
noncomputable def excision (hS : S ⊆ A ∪ B) (hB : ∀ c : ZMod p, ∀ x ∈ B, c +ᵥ x ∈ B) :
    Σ r : DualFunctor (FiltQuot (suppIn (G := G) S B))
        (FiltQuot (ExcisivePair.inter (suppIn (G := G) S A) (suppIn S B))),
      DualFunctor.UnitaryIso (DualFunctor.id _)
          ((ExcisivePair.e (suppIn (G := G) S A) (suppIn S B)).comp r) ×
        DualFunctor.UnitaryIso (r.comp (ExcisivePair.e (suppIn (G := G) S A)
          (suppIn S B))) (DualFunctor.id _) :=
  ⟨exR S A B hS hB,
    { iso := NatIso.ofComponents (fun M =>
          { hom := (FiltQuot.functor _).map (ObjectProperty.homMk (exPro S A M.as.obj) :
              M.as ⟶ exObj S A M.as.obj)
            inv := (FiltQuot.functor _).map (ObjectProperty.homMk (exInc S A M.as.obj) :
              exObj S A M.as.obj ⟶ M.as)
            hom_inv_id := unit_hom_inv S A B hS M
            inv_hom_id := unit_inv_hom S A B M }) (by
          intro M N f
          obtain ⟨g, rfl⟩ := FiltQuot.functor_map_surjective _ f
          show (FiltQuot.functor (ExcisivePair.inter (suppIn (G := G) S A) (suppIn S B))).map g ≫ (FiltQuot.functor (ExcisivePair.inter (suppIn (G := G) S A) (suppIn S B))).map (ObjectProperty.homMk (exPro S A N.as.obj) :
              N.as ⟶ exObj S A N.as.obj) =
            (FiltQuot.functor (ExcisivePair.inter (suppIn (G := G) S A) (suppIn S B))).map (ObjectProperty.homMk (exPro S A M.as.obj) : M.as ⟶ exObj S A M.as.obj) ≫
              (FiltQuot.functor (ExcisivePair.inter (suppIn (G := G) S A) (suppIn S B))).map (exMap S A g.hom)
          rw [← Functor.map_comp, ← Functor.map_comp, FiltQuot.functor_map_eq_iff]
          have he : g ≫ (ObjectProperty.homMk (exPro S A N.as.obj) :
                N.as ⟶ exObj S A N.as.obj) -
              (ObjectProperty.homMk (exPro S A M.as.obj) : M.as ⟶ exObj S A M.as.obj) ≫
                exMap S A g.hom =
              (ObjectProperty.homMk (exFarPro S A M.as.obj) :
                  M.as ⟶ ⟨exFar S A M.as.obj, supp_restrict M.as.property _⟩) ≫
                ObjectProperty.homMk (exFarInc S A M.as.obj ≫ g.hom ≫ exPro S A N.as.obj) := by
            refine ObjectProperty.hom_ext _ ?_
            change g.hom ≫ exPro S A N.as.obj -
                exPro S A M.as.obj ≫ exInc S A M.as.obj ≫ g.hom ≫ exPro S A N.as.obj =
              exFarPro S A M.as.obj ≫ exFarInc S A M.as.obj ≫ g.hom ≫ exPro S A N.as.obj
            rw [← Category.assoc (exFarPro S A M.as.obj), ← one_sub_exPro_exInc]
            simp only [Preadditive.sub_comp, Category.id_comp, Category.assoc]
          rw [he]
          exact ⟨_, supp_exFar S A B hS M.as.obj, _, _, rfl⟩)
      unitary M := by
        have hξ : (exR S A B hS hB).toFunctor.map ((ExcisivePair.e (suppIn (G := G) S A) (suppIn S B)).ξ M).hom ≫
            ((exR S A B hS hB).ξ ((ExcisivePair.e (suppIn (G := G) S A) (suppIn S B)).toFunctor.obj M)).hom = 𝟙 _ := by
          change (exR S A B hS hB).toFunctor.map (𝟙 _) ≫ 𝟙 _ = 𝟙 _
          rw [CategoryTheory.Functor.map_id, Category.comp_id]
        simp only [DualFunctor.id_ξ, DualFunctor.comp_ξ, Iso.refl_hom, Iso.trans_hom,
          Functor.mapIso_hom, NatIso.ofComponents_hom_app]
        rw [hξ]
        have hd : dualHom (ObjectProperty.homMk (exPro S A M.as.obj) :
            M.as ⟶ exObj S A M.as.obj) = ObjectProperty.homMk (exInc S A M.as.obj) :=
          ObjectProperty.hom_ext _ (dualHom_exPro S A M.as.obj)
        show (FiltQuot.functor (ExcisivePair.inter (suppIn (G := G) S A) (suppIn S B))).map (ObjectProperty.homMk (exPro S A M.as.obj) : M.as ⟶ exObj S A M.as.obj) ≫
          𝟙 _ ≫ dualHom ((FiltQuot.functor (ExcisivePair.inter (suppIn (G := G) S A) (suppIn S B))).map (ObjectProperty.homMk (exPro S A M.as.obj) :
            M.as ⟶ exObj S A M.as.obj)) = 𝟙 M
        rw [Category.id_comp, FiltQuot.dualHom_map, hd]
        exact unit_hom_inv S A B hS M },
    { iso := NatIso.ofComponents (fun M =>
          { hom := (FiltQuot.functor _).map (exInc S A M.as)
            inv := (FiltQuot.functor _).map (exPro S A M.as)
            hom_inv_id := counit_hom_inv S A B M
            inv_hom_id := counit_inv_hom S A B hS M }) (by
          intro M N f
          obtain ⟨u, rfl⟩ := FiltQuot.functor_map_surjective _ f
          show (FiltQuot.functor (suppIn S B)).map (exInc S A M.as ≫ u ≫ exPro S A N.as) ≫
              (FiltQuot.functor (suppIn S B)).map (exInc S A N.as) =
            (FiltQuot.functor (suppIn S B)).map (exInc S A M.as) ≫
              (FiltQuot.functor (suppIn S B)).map u
          rw [← Functor.map_comp, ← Functor.map_comp, FiltQuot.functor_map_eq_iff]
          have he : (exInc S A M.as ≫ u ≫ exPro S A N.as) ≫ exInc S A N.as -
              exInc S A M.as ≫ u = -(exInc S A M.as ≫ u ≫
                (𝟙 N.as - exPro S A N.as ≫ exInc S A N.as)) := by
            simp only [Preadditive.comp_sub, Category.comp_id, Category.assoc, neg_sub]
          rw [he]
          exact FiltQuot.ideal_neg (FiltQuot.ideal_comp_left _ (FiltQuot.ideal_comp_left _
            (ideal_one_sub S A B hS N.as))))
      unitary M := by
        have hξ : (ExcisivePair.e (suppIn (G := G) S A) (suppIn S B)).toFunctor.map ((exR S A B hS hB).ξ M).hom ≫
            ((ExcisivePair.e (suppIn (G := G) S A) (suppIn S B)).ξ ((exR S A B hS hB).toFunctor.obj M)).hom = 𝟙 _ := by
          change (ExcisivePair.e (suppIn (G := G) S A) (suppIn S B)).toFunctor.map (𝟙 _) ≫ 𝟙 _ = 𝟙 _
          rw [CategoryTheory.Functor.map_id, Category.comp_id]
        simp only [DualFunctor.id_ξ, DualFunctor.comp_ξ, Iso.refl_hom, Iso.trans_hom,
          Functor.mapIso_hom, NatIso.ofComponents_hom_app]
        rw [hξ]
        show (FiltQuot.functor (suppIn S B)).map (exInc S A M.as) ≫ 𝟙 _ ≫
          dualHom ((FiltQuot.functor (suppIn S B)).map (exInc S A M.as)) = 𝟙 _
        rw [Category.id_comp, FiltQuot.dualHom_map, dualHom_exInc]
        exact counit_hom_inv S A B M }⟩

end Excision

end HSP
