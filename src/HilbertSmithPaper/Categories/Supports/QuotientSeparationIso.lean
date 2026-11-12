import HilbertSmithPaper.Categories.Supports.QuotientSupportAdditive
import HilbertSmithPaper.Categories.Supports.DisjointSupportVanishing
import HilbertSmithPaper.Categories.Supports.SupportDualAdditive

/-!
# Separated support in a quotient

Let `X` be compact with an isometric `C_p`-action, `S ⊆ X`, and `Y, Z ⊆ X` closed and invariant with
`Y ⊆ S` and `Y ∩ Z = ∅`. The quotient functor `𝒜_Y → 𝒰_Y ⊂ 𝒜_S/𝒜_Z`, `M ↦ ⟨M⟩`, `u ↦ [u]`, and its
inverse, the identity on objects, are mutually inverse strict duality functors
(`HSP.quotientSeparationIso`, a subtype of pairs of duality functors). The quotient functor is
full, and faithful because two representatives between `Y`-supported objects with the same class
differ by a map through `𝒜_Z`, which vanishes (`HSP.mkHom_eq_zero_of_disjoint`); the inverse is
the inverse bijection on hom-sets.

Lean encoding. The functors are first built for an arbitrary duality category `A` with
dual-closed additive subcategories `P_Y ≤ P_S`, `U` of `P_S`, and `Q` of `P_S/U` with
`Q ⟨M⟩ ↔ P_Y M`, given that the quotient map is injective on maps into `P_Y`; the result is the
instance `A = 𝒜_𝐆(X)`, `P_Y = 𝒜_Y`, `P_S = 𝒜_S`, `U = 𝒜_Z`, `Q = 𝒰_Y`. (Working with abstract
subcategories keeps the kernel from unfolding the support predicates when it compares objects of
different subcategories.)
-/

open CategoryTheory CategoryTheory.Limits Filter Metric

namespace HSP

open DualCat

section Generic

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]

private instance {P P' : ObjectProperty A} (h : P ≤ P') : (ObjectProperty.ιOfLE h).Additive where
  map_add := rfl

private instance {P P' : ObjectProperty A} (h : P ≤ P') :
    (ObjectProperty.ιOfLE h).Linear ℚ where
  map_smul _ _ := rfl

variable {PY PS : ObjectProperty A} [IsDualAdditive PY] [IsDualAdditive PS]
  {U : ObjectProperty PS.FullSubcategory} [IsDualAdditive U]
  {Q : ObjectProperty (FiltQuot U)} [IsDualAdditive Q]

/-- The quotient functor `P_Y → Q ⊂ P_S/U`. -/
private abbrev sepFunctor (hle : PY ≤ PS) (hQ : ∀ M, Q M ↔ PY M.as.obj) :
    PY.FullSubcategory ⥤ Q.FullSubcategory :=
  ObjectProperty.lift _ (ObjectProperty.ιOfLE hle ⋙ FiltQuot.functor U)
    (fun M => (hQ _).2 M.property)

private instance (hle : PY ≤ PS) (hQ : ∀ M, Q M ↔ PY M.as.obj) :
    (sepFunctor hle hQ).Additive where
  map_add {_ _ f g} := ObjectProperty.hom_ext _
    ((ObjectProperty.ιOfLE hle ⋙ FiltQuot.functor U).map_add (f := f) (g := g))

private instance (hle : PY ≤ PS) (hQ : ∀ M, Q M ↔ PY M.as.obj) :
    (sepFunctor hle hQ).Linear ℚ where
  map_smul {_ _} f c := ObjectProperty.hom_ext _
    ((ObjectProperty.ιOfLE hle ⋙ FiltQuot.functor U).map_smul c f)

private theorem sep_map_dualHom (hle : PY ≤ PS) (hQ : ∀ M, Q M ↔ PY M.as.obj)
    {M N : PY.FullSubcategory} (f : M ⟶ N) :
    (sepFunctor hle hQ).map (dualHom f) = dualHom ((sepFunctor hle hQ).map f) :=
  ObjectProperty.hom_ext _ rfl

/-- The quotient functor as a strict duality functor. -/
private def sepDual (hle : PY ≤ PS) (hQ : ∀ M, Q M ↔ PY M.as.obj) :
    DualFunctor PY.FullSubcategory Q.FullSubcategory where
  toFunctor := sepFunctor hle hQ
  ξ _ := Iso.refl _
  ξ_natural f :=
    (Category.comp_id _).trans ((sep_map_dualHom hle hQ f).trans (Category.id_comp _).symm)
  ξ_dual _ := (dualHom_id _).trans ((eqToHom_refl _ _).symm.trans (Category.comp_id _).symm)

private instance (hle : PY ≤ PS) (hQ : ∀ M, Q M ↔ PY M.as.obj) :
    (sepFunctor hle hQ).Full where
  map_surjective {M N} f := by
    obtain ⟨g, hg⟩ := (FiltQuot.functor U).map_surjective f.hom
    exact ⟨ObjectProperty.homMk g.hom, ObjectProperty.hom_ext _ hg⟩

/-- The quotient functor is fully faithful, given that the quotient map is injective on maps
into objects of `P_Y`. -/
private noncomputable def sepFull (hle : PY ≤ PS) (hQ : ∀ M, Q M ↔ PY M.as.obj)
    (hinj : ∀ {P R : PS.FullSubcategory}, PY R.obj → ∀ {g g' : P ⟶ R},
      (FiltQuot.functor U).map g = (FiltQuot.functor U).map g' → g = g') :
    (sepFunctor hle hQ).FullyFaithful :=
  have : (sepFunctor hle hQ).Faithful := ⟨fun {M N} f g h =>
    ObjectProperty.hom_ext _ (by
      have := hinj (P := (ObjectProperty.ιOfLE hle).obj M) (R := (ObjectProperty.ιOfLE hle).obj N)
        N.property (g := (ObjectProperty.ιOfLE hle).map f)
        (g' := (ObjectProperty.ιOfLE hle).map g) (congrArg (fun f => f.hom) h)
      exact congrArg (fun f => f.hom) this)⟩
  .ofFullyFaithful _

/-- The inverse functor `Q → P_Y`: the identity on objects, the preimage on maps. -/
private noncomputable def sepInvFunctor (hle : PY ≤ PS) (hQ : ∀ M, Q M ↔ PY M.as.obj)
    (hinj : ∀ {P R : PS.FullSubcategory}, PY R.obj → ∀ {g g' : P ⟶ R},
      (FiltQuot.functor U).map g = (FiltQuot.functor U).map g' → g = g') :
    Q.FullSubcategory ⥤ PY.FullSubcategory where
  obj M := ⟨M.obj.as.obj, (hQ _).1 M.property⟩
  map {M N} f := (sepFull hle hQ hinj).preimage
    (X := ⟨M.obj.as.obj, (hQ _).1 M.property⟩) (Y := ⟨N.obj.as.obj, (hQ _).1 N.property⟩) f
  map_id M := (sepFull hle hQ hinj).map_injective (by
    refine ((sepFull hle hQ hinj).map_preimage _).trans ?_
    exact ((sepFunctor hle hQ).map_id ⟨M.obj.as.obj, (hQ _).1 M.property⟩).symm)
  map_comp {L M N} f g := (sepFull hle hQ hinj).map_injective (by
    refine ((sepFull hle hQ hinj).map_preimage _).trans ?_
    refine Eq.trans ?_ ((sepFunctor hle hQ).map_comp _ _).symm
    rw [(sepFull hle hQ hinj).map_preimage, (sepFull hle hQ hinj).map_preimage])

omit [Linear ℚ A] [HasFiniteBiproducts A] [DualCat A] [IsDualAdditive PY] [IsDualAdditive PS]
  [IsDualAdditive U] [IsDualAdditive Q] in
private theorem sepInv_spec (hle : PY ≤ PS) (hQ : ∀ M, Q M ↔ PY M.as.obj)
    (hinj : ∀ {P R : PS.FullSubcategory}, PY R.obj → ∀ {g g' : P ⟶ R},
      (FiltQuot.functor U).map g = (FiltQuot.functor U).map g' → g = g')
    {M N : Q.FullSubcategory} (f : M ⟶ N) :
    (sepFunctor hle hQ).map ((sepInvFunctor hle hQ hinj).map f) = f :=
  (sepFull hle hQ hinj).map_preimage _

private instance (hle : PY ≤ PS) (hQ : ∀ M, Q M ↔ PY M.as.obj)
    (hinj : ∀ {P R : PS.FullSubcategory}, PY R.obj → ∀ {g g' : P ⟶ R},
      (FiltQuot.functor U).map g = (FiltQuot.functor U).map g' → g = g') :
    (sepInvFunctor hle hQ hinj).Additive where
  map_add {_ _ f g} := (sepFull hle hQ hinj).map_injective (by
    rw [sepInv_spec, (sepFunctor hle hQ).map_add, sepInv_spec, sepInv_spec]
    rfl)

private instance (hle : PY ≤ PS) (hQ : ∀ M, Q M ↔ PY M.as.obj)
    (hinj : ∀ {P R : PS.FullSubcategory}, PY R.obj → ∀ {g g' : P ⟶ R},
      (FiltQuot.functor U).map g = (FiltQuot.functor U).map g' → g = g') :
    (sepInvFunctor hle hQ hinj).Linear ℚ where
  map_smul f c := (sepFull hle hQ hinj).map_injective (by
    rw [sepInv_spec, (sepFunctor hle hQ).map_smul, sepInv_spec]
    rfl)

/-- The inverse functor as a strict duality functor. -/
private noncomputable def sepInvDual (hle : PY ≤ PS) (hQ : ∀ M, Q M ↔ PY M.as.obj)
    (hinj : ∀ {P R : PS.FullSubcategory}, PY R.obj → ∀ {g g' : P ⟶ R},
      (FiltQuot.functor U).map g = (FiltQuot.functor U).map g' → g = g') :
    DualFunctor Q.FullSubcategory PY.FullSubcategory where
  toFunctor := sepInvFunctor hle hQ hinj
  ξ _ := Iso.refl _
  ξ_natural {M N} f := by
    refine (Category.comp_id _).trans (Eq.trans ?_ (Category.id_comp _).symm)
    refine (sepFull hle hQ hinj).map_injective ?_
    have h1 := sepInv_spec hle hQ hinj (dualHom f)
    have h2 := sep_map_dualHom hle hQ ((sepInvFunctor hle hQ hinj).map f)
    rw [sepInv_spec hle hQ hinj f] at h2
    exact h1.trans h2.symm
  ξ_dual _ := (dualHom_id _).trans ((eqToHom_refl _ _).symm.trans (Category.comp_id _).symm)

/-- The separated-support isomorphism for abstract subcategories. -/
private noncomputable def sepIso (hle : PY ≤ PS) (hQ : ∀ M, Q M ↔ PY M.as.obj)
    (hinj : ∀ {P R : PS.FullSubcategory}, PY R.obj → ∀ {g g' : P ⟶ R},
      (FiltQuot.functor U).map g = (FiltQuot.functor U).map g' → g = g') :
    {e : DualFunctor PY.FullSubcategory Q.FullSubcategory ×
        DualFunctor Q.FullSubcategory PY.FullSubcategory //
      e.1.toFunctor ⋙ Q.ι = ObjectProperty.ιOfLE hle ⋙ FiltQuot.functor U ∧
        e.1.IsStrict ∧ e.2.IsStrict ∧ e.1.toFunctor ⋙ e.2.toFunctor = 𝟭 _ ∧
        e.2.toFunctor ⋙ e.1.toFunctor = 𝟭 _} :=
  ⟨(sepDual hle hQ, sepInvDual hle hQ hinj), rfl, fun _ => ⟨rfl, rfl⟩,
    fun _ => ⟨rfl, rfl⟩,
    CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ f => by
      erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
      exact (sepFull hle hQ hinj).map_injective
        (sepInv_spec hle hQ hinj ((sepFunctor hle hQ).map f))),
    CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ f => by
      erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
      exact sepInv_spec hle hQ hinj f)⟩

end Generic

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]
  [IsIsometricVAdd (ZMod p) X]

section

variable [CompactSpace X] {S Y Z : Set X}

/-- The quotient map `𝒜_S → 𝒜_S/𝒜_Z` is injective on maps into `Y`-supported objects. -/
private theorem map_injective (hY : IsClosed Y) (hZ : IsClosed Z)
    (hYi : ∀ c : ZMod p, ∀ x ∈ Y, c +ᵥ x ∈ Y) (hZi : ∀ c : ZMod p, ∀ x ∈ Z, c +ᵥ x ∈ Z)
    (hYZ : Disjoint Y Z) {P Q : (supp S : ObjectProperty (AsymCat G X)).FullSubcategory}
    (hQ : supp Y Q.obj) {g g' : P ⟶ Q}
    (h : (FiltQuot.functor (suppIn S Z)).map g = (FiltQuot.functor (suppIn S Z)).map g') :
    g = g' := by
  rw [FiltQuot.functor_map_eq_iff] at h
  obtain ⟨V, hV, a, b, hab⟩ := h
  obtain ⟨u, hu⟩ := AsymCat.mkHom_surjective (g.hom - g'.hom)
  have hI : FiltQuot.ideal (supp Z) (AsymCat.mkHom u) :=
    ⟨V.obj, hV, a.hom, b.hom, by rw [hu]; exact congrArg (fun f => f.hom) hab⟩
  have h0 := mkHom_eq_zero_of_disjoint hY hZ hYi hZi hYZ hQ u hI
  refine ObjectProperty.hom_ext _ (sub_eq_zero.1 ?_)
  rw [← hu, h0]

omit [IsIsometricVAdd (ZMod p) X] [CompactSpace X] in
private theorem supp_le (hYS : Y ⊆ S) : (supp Y : ObjectProperty (AsymCat G X)) ≤ supp S :=
  fun _ hM ε hε => (hM ε hε).mono fun _ hi k => thickening_subset_of_subset ε hYS (hi k)

end

/-- **Separated support in a quotient.** Let `X` be compact with an isometric `C_p`-action,
`S ⊆ X`, and `Y, Z ⊆ X` closed and invariant with `Y ⊆ S` and `Y ∩ Z = ∅`. The quotient functor
`𝒜_Y → 𝒰_Y ⊂ 𝒜_S/𝒜_Z` (`e.1`, characterized by `e.1 ⋙ ι = ι_{Y ⊆ S} ⋙ q`) and its inverse `e.2`
are mutually inverse strict duality functors. -/
noncomputable def quotientSeparationIso [CompactSpace X] (S : Set X) {Y Z : Set X}
    (hY : IsClosed Y) (hZ : IsClosed Z) (hYi : ∀ c : ZMod p, ∀ x ∈ Y, c +ᵥ x ∈ Y)
    (hZi : ∀ c : ZMod p, ∀ x ∈ Z, c +ᵥ x ∈ Z) (hYZ : Disjoint Y Z) (hYS : Y ⊆ S) :
    {e : DualFunctor (supp Y : ObjectProperty (AsymCat G X)).FullSubcategory
          (quotSupp (G := G) S Z Y).FullSubcategory ×
        DualFunctor (quotSupp (G := G) S Z Y).FullSubcategory
          (supp Y : ObjectProperty (AsymCat G X)).FullSubcategory //
      e.1.toFunctor ⋙ (quotSupp S Z Y).ι =
          ObjectProperty.ιOfLE (fun _ hM ε hε => (hM ε hε).mono fun _ hi k =>
            thickening_subset_of_subset ε hYS (hi k)) ⋙ FiltQuot.functor (suppIn S Z) ∧
        e.1.IsStrict ∧ e.2.IsStrict ∧ e.1.toFunctor ⋙ e.2.toFunctor = 𝟭 _ ∧
        e.2.toFunctor ⋙ e.1.toFunctor = 𝟭 _} :=
  sepIso (supp_le hYS) (fun _ => Iff.rfl) (map_injective hY hZ hYi hZi hYZ)

end HSP
