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
-/

open CategoryTheory CategoryTheory.Limits Filter Metric

namespace HSP

open DualCat

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

private instance {P P' : ObjectProperty (AsymCat G X)} (h : P ≤ P') :
    (ObjectProperty.ιOfLE h).Additive where
  map_add := rfl

private instance {P P' : ObjectProperty (AsymCat G X)} (h : P ≤ P') :
    (ObjectProperty.ιOfLE h).Linear ℚ where
  map_smul _ _ := rfl

omit [IsIsometricVAdd (ZMod p) X] [CompactSpace X] in
private theorem supp_le (hYS : Y ⊆ S) : (supp Y : ObjectProperty (AsymCat G X)) ≤ supp S :=
  fun _ hM ε hε => (hM ε hε).mono fun _ hi k => thickening_subset_of_subset ε hYS (hi k)

variable (S Z) in
/-- The quotient functor `𝒜_Y → 𝒰_Y ⊂ 𝒜_S/𝒜_Z`. -/
private abbrev sepFunctor (hYS : Y ⊆ S) :
    (supp Y : ObjectProperty (AsymCat G X)).FullSubcategory ⥤
      (quotSupp (G := G) S Z Y).FullSubcategory :=
  ObjectProperty.lift _ (ObjectProperty.ιOfLE (supp_le hYS) ⋙ FiltQuot.functor (suppIn S Z))
    (fun M => M.property)

private instance (hYS : Y ⊆ S) : (sepFunctor (G := G) S Z hYS).Additive where
  map_add {_ _ f g} := ObjectProperty.hom_ext _
    ((ObjectProperty.ιOfLE _ ⋙ FiltQuot.functor (suppIn S Z)).map_add (f := f) (g := g))

private instance (hYS : Y ⊆ S) : (sepFunctor (G := G) S Z hYS).Linear ℚ where
  map_smul {_ _} f c := ObjectProperty.hom_ext _
    ((ObjectProperty.ιOfLE _ ⋙ FiltQuot.functor (suppIn S Z)).map_smul c f)

omit [IsIsometricVAdd (ZMod p) X] [CompactSpace X] in
private theorem sep_map_dualHom (hYS : Y ⊆ S)
    {M N : (supp Y : ObjectProperty (AsymCat G X)).FullSubcategory} (f : M ⟶ N) :
    (sepFunctor (G := G) S Z hYS).map (dualHom f) = dualHom ((sepFunctor (G := G) S Z hYS).map f) :=
  ObjectProperty.hom_ext _ rfl

variable (S Z) in
/-- The quotient functor as a strict duality functor. -/
private def sepDual (hYS : Y ⊆ S) :
    DualFunctor (supp Y : ObjectProperty (AsymCat G X)).FullSubcategory
      (quotSupp (G := G) S Z Y).FullSubcategory where
  toFunctor := sepFunctor (G := G) S Z hYS
  ξ _ := Iso.refl _
  ξ_natural f :=
    (Category.comp_id _).trans ((sep_map_dualHom hYS f).trans (Category.id_comp _).symm)
  ξ_dual _ := (dualHom_id _).trans ((eqToHom_refl _ _).symm.trans (Category.comp_id _).symm)

private instance (hYS : Y ⊆ S) : (sepFunctor (G := G) S Z hYS).Full where
  map_surjective {M N} f := by
    obtain ⟨g, hg⟩ := (FiltQuot.functor (suppIn S Z)).map_surjective f.hom
    exact ⟨ObjectProperty.homMk g.hom, ObjectProperty.hom_ext _ hg⟩

variable (S Z) in
/-- The quotient functor is fully faithful. -/
private noncomputable def sepFull (hY : IsClosed Y) (hZ : IsClosed Z)
    (hYi : ∀ c : ZMod p, ∀ x ∈ Y, c +ᵥ x ∈ Y) (hZi : ∀ c : ZMod p, ∀ x ∈ Z, c +ᵥ x ∈ Z)
    (hYZ : Disjoint Y Z) (hYS : Y ⊆ S) : (sepFunctor (G := G) S Z hYS).FullyFaithful :=
  have : (sepFunctor (G := G) S Z hYS).Faithful := ⟨fun {M N} f g h =>
    ObjectProperty.hom_ext _ (by
      have := map_injective (S := S) hY hZ hYi hZi hYZ N.property
        (g := (ObjectProperty.ιOfLE (supp_le hYS)).map f)
        (g' := (ObjectProperty.ιOfLE (supp_le hYS)).map g) (congrArg (fun f => f.hom) h)
      exact congrArg (fun f => f.hom) this)⟩
  .ofFullyFaithful _

variable (S Z) in
/-- The inverse functor `𝒰_Y → 𝒜_Y`: the identity on objects, the preimage on maps. -/
private noncomputable def sepInvFunctor (hY : IsClosed Y) (hZ : IsClosed Z)
    (hYi : ∀ c : ZMod p, ∀ x ∈ Y, c +ᵥ x ∈ Y) (hZi : ∀ c : ZMod p, ∀ x ∈ Z, c +ᵥ x ∈ Z)
    (hYZ : Disjoint Y Z) (hYS : Y ⊆ S) :
    (quotSupp (G := G) S Z Y).FullSubcategory ⥤
      (supp Y : ObjectProperty (AsymCat G X)).FullSubcategory where
  obj M := ⟨M.obj.as.obj, M.property⟩
  map {M N} f := (sepFull (G := G) S Z hY hZ hYi hZi hYZ hYS).preimage
    (X := ⟨M.obj.as.obj, M.property⟩) (Y := ⟨N.obj.as.obj, N.property⟩) f
  map_id M := (sepFull (G := G) S Z hY hZ hYi hZi hYZ hYS).map_injective (by
    refine ((sepFull (G := G) S Z hY hZ hYi hZi hYZ hYS).map_preimage _).trans ?_
    exact ((sepFunctor (G := G) S Z hYS).map_id ⟨M.obj.as.obj, M.property⟩).symm)
  map_comp {L M N} f g := (sepFull (G := G) S Z hY hZ hYi hZi hYZ hYS).map_injective (by
    refine ((sepFull (G := G) S Z hY hZ hYi hZi hYZ hYS).map_preimage _).trans ?_
    refine Eq.trans ?_ ((sepFunctor (G := G) S Z hYS).map_comp _ _).symm
    rw [(sepFull (G := G) S Z hY hZ hYi hZi hYZ hYS).map_preimage,
      (sepFull (G := G) S Z hY hZ hYi hZi hYZ hYS).map_preimage])

private theorem sepInv_spec (hY : IsClosed Y) (hZ : IsClosed Z)
    (hYi : ∀ c : ZMod p, ∀ x ∈ Y, c +ᵥ x ∈ Y) (hZi : ∀ c : ZMod p, ∀ x ∈ Z, c +ᵥ x ∈ Z)
    (hYZ : Disjoint Y Z) (hYS : Y ⊆ S) {M N : (quotSupp (G := G) S Z Y).FullSubcategory}
    (f : M ⟶ N) :
    (sepFunctor (G := G) S Z hYS).map ((sepInvFunctor (G := G) S Z hY hZ hYi hZi hYZ hYS).map f) =
      f :=
  (sepFull (G := G) S Z hY hZ hYi hZi hYZ hYS).map_preimage _

private instance (hY : IsClosed Y) (hZ : IsClosed Z)
    (hYi : ∀ c : ZMod p, ∀ x ∈ Y, c +ᵥ x ∈ Y) (hZi : ∀ c : ZMod p, ∀ x ∈ Z, c +ᵥ x ∈ Z)
    (hYZ : Disjoint Y Z) (hYS : Y ⊆ S) :
    (sepInvFunctor (G := G) S Z hY hZ hYi hZi hYZ hYS).Additive where
  map_add {_ _ f g} := (sepFull (G := G) S Z hY hZ hYi hZi hYZ hYS).map_injective (by
    rw [sepInv_spec, (sepFunctor (G := G) S Z hYS).map_add, sepInv_spec, sepInv_spec]
    rfl)

private instance (hY : IsClosed Y) (hZ : IsClosed Z)
    (hYi : ∀ c : ZMod p, ∀ x ∈ Y, c +ᵥ x ∈ Y) (hZi : ∀ c : ZMod p, ∀ x ∈ Z, c +ᵥ x ∈ Z)
    (hYZ : Disjoint Y Z) (hYS : Y ⊆ S) :
    (sepInvFunctor (G := G) S Z hY hZ hYi hZi hYZ hYS).Linear ℚ where
  map_smul f c := (sepFull (G := G) S Z hY hZ hYi hZi hYZ hYS).map_injective (by
    rw [sepInv_spec, (sepFunctor (G := G) S Z hYS).map_smul, sepInv_spec]
    rfl)

variable (S Z) in
/-- The inverse functor as a strict duality functor. -/
private noncomputable def sepInvDual (hY : IsClosed Y) (hZ : IsClosed Z)
    (hYi : ∀ c : ZMod p, ∀ x ∈ Y, c +ᵥ x ∈ Y) (hZi : ∀ c : ZMod p, ∀ x ∈ Z, c +ᵥ x ∈ Z)
    (hYZ : Disjoint Y Z) (hYS : Y ⊆ S) :
    DualFunctor (quotSupp (G := G) S Z Y).FullSubcategory
      (supp Y : ObjectProperty (AsymCat G X)).FullSubcategory where
  toFunctor := sepInvFunctor (G := G) S Z hY hZ hYi hZi hYZ hYS
  ξ _ := Iso.refl _
  ξ_natural {M N} f := by
    refine (Category.comp_id _).trans (Eq.trans ?_ (Category.id_comp _).symm)
    refine (sepFull (G := G) S Z hY hZ hYi hZi hYZ hYS).map_injective ?_
    rw [sepInv_spec, sep_map_dualHom, sepInv_spec]
    rfl
  ξ_dual _ := (dualHom_id _).trans ((eqToHom_refl _ _).symm.trans (Category.comp_id _).symm)

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
  ⟨(sepDual S Z hYS, sepInvDual S Z hY hZ hYi hZi hYZ hYS), rfl, fun _ => ⟨rfl, rfl⟩,
    fun _ => ⟨rfl, rfl⟩,
    CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ f => by
      erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
      exact (sepFull (G := G) S Z hY hZ hYi hZi hYZ hYS).map_injective
        (sepInv_spec hY hZ hYi hZi hYZ hYS ((sepFunctor (G := G) S Z hYS).map f))),
    CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ f => by
      erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
      exact sepInv_spec hY hZ hYi hZi hYZ hYS f)⟩

end HSP
