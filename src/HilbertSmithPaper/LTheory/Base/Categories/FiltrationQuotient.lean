import HilbertSmithPaper.LTheory.Base.Categories.DualityFunctor
import HilbertSmithPaper.LTheory.Base.Categories.DualAdditiveSubcategory
import HilbertSmithPaper.LTheory.Base.Categories.FiltrationIdealClosure

/-!
# Quotient by a subcategory

For a full additive subcategory `𝒰 ⊂ 𝒜` closed under duality (`HSP.IsDualAdditive U`), the maps
factoring through an object of `𝒰` form a ℚ-linear ideal `I_𝒰` closed under `*`
(`FiltQuot.ideal`, `FiltQuot.ideal_closed`). The quotient `𝒜/𝒰` is Mathlib's `CategoryTheory.Quotient` by the relation
`f ~ g ⇔ f - g ∈ I_𝒰` (`FiltQuot.rel`), a congruence compatible with sums and scalars, so it
carries `Quotient.preadditive` and `Quotient.linear`. Its finite biproducts are the images of
those of `𝒜` under the additive quotient functor, and its duality is `⟨M⟩^* = ⟨M^*⟩`,
`[f]^* = [f^*]`.

`FiltQuot U` is an `abbrev` for `Quotient (FiltQuot.rel U)`; the preadditive, linear, biproduct
and duality instances are registered on it (they need `[IsDualAdditive U]`).
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]

namespace FiltQuot

/-- The relation `f ~ g ⇔ f - g ∈ I_𝒰` whose quotient is `𝒜/𝒰`. -/
def rel (U : ObjectProperty A) : HomRel A := fun _ _ f g => ideal U (f - g)

variable {U : ObjectProperty A}

instance [IsDualAdditive U] : Congruence (rel U) where
  equivalence :=
    { refl _ := by simpa [rel] using (ideal_closed U).1
      symm {f g} h := by simpa [rel] using (ideal_closed U).2.2.1 h
      trans {f g k} h₁ h₂ := by simpa [rel] using (ideal_closed U).2.1 h₁ h₂ }
  comp_left := by
    intro _ _ _ h _ _ hfg
    simpa [rel, Preadditive.comp_sub] using (ideal_closed U).2.2.2.2.1 h hfg
  comp_right := by
    intro _ _ _ _ _ h hfg
    simpa [rel, Preadditive.sub_comp] using (ideal_closed U).2.2.2.2.2.1 hfg h

private lemma rel_add [IsDualAdditive U] ⦃M N : A⦄ (f₁ f₂ g₁ g₂ : M ⟶ N) (h₁ : rel U f₁ f₂)
    (h₂ : rel U g₁ g₂) : rel U (f₁ + g₁) (f₂ + g₂) := by
  have := (ideal_closed U).2.1 h₁ h₂
  unfold rel
  convert this using 1
  abel

private lemma rel_smul [IsDualAdditive U] (c : ℚ) ⦃M N : A⦄ (f₁ f₂ : M ⟶ N) (h : rel U f₁ f₂) :
    rel U (c • f₁) (c • f₂) := by
  simpa [rel, smul_sub] using (ideal_closed U).2.2.2.1 c h

end FiltQuot

/-- The *quotient* `𝒜/𝒰` of a duality category by a full additive subcategory closed under
duality: the objects of `𝒜`, with `Hom(M, N) / I_𝒰(M, N)`. It is a duality category. -/
abbrev FiltQuot (U : ObjectProperty A) : Type u := Quotient (FiltQuot.rel U)

namespace FiltQuot

variable (U : ObjectProperty A)

/-- The quotient functor `𝒜 ⥤ 𝒜/𝒰`, `M ↦ ⟨M⟩`, `f ↦ [f]`. -/
abbrev functor : A ⥤ FiltQuot U := Quotient.functor (rel U)

variable [IsDualAdditive U]

instance : Preadditive (FiltQuot U) := Quotient.preadditive (rel U) rel_add

instance : (functor U).Additive where
  map_add := rfl

instance : Linear ℚ (FiltQuot U) :=
  letI : Preadditive (Quotient (rel U)) := Quotient.preadditive (rel U) rel_add
  haveI : (Quotient.functor (rel U)).Additive := Quotient.functor_additive (rel U) rel_add
  Quotient.linear ℚ (rel U) rel_smul

instance : (functor U).Linear ℚ where
  map_smul _ _ := rfl

omit [Linear ℚ A] [HasFiniteBiproducts A] [DualCat A] [IsDualAdditive U] in
lemma functor_obj (M : A) : (functor U).obj M = ⟨M⟩ := rfl

lemma functor_map_eq_iff {M N : A} (f g : M ⟶ N) :
    (functor U).map f = (functor U).map g ↔ ideal U (f - g) :=
  Quotient.functor_map_eq_iff (rel U) f g

instance : HasFiniteBiproducts (FiltQuot U) where
  out _ := ⟨fun f => HasBiproduct.mk
    { bicone := (functor U).mapBicone (biproduct.bicone fun j => (f j).as)
      isBilimit := isBilimitOfPreserves (functor U) (biproduct.isBilimit _) }⟩

/-- The duality on morphisms of `𝒜/𝒰`: `[f]^* = [f^*]`, well defined since `I_𝒰` is closed
under `*`. -/
private def dualHomQ {M N : FiltQuot U} (f : M ⟶ N) :
    (functor U).obj (dual N.as) ⟶ (functor U).obj (dual M.as) :=
  Quot.liftOn f (fun g => (functor U).map (dualHom g)) fun g g' h => by
    rw [HomRel.compClosure_iff_self] at h
    rw [functor_map_eq_iff, ← dualHom_sub]
    exact (ideal_closed U).2.2.2.2.2.2 h

private lemma dualHomQ_map {M N : A} (g : M ⟶ N) :
    dualHomQ U ((functor U).map g) = (functor U).map (dualHom g) := rfl

private lemma dualHomQ_id (M : A) :
    dualHomQ U (𝟙 ((functor U).obj M)) = 𝟙 ((functor U).obj (dual M)) := by
  rw [← (functor U).map_id M, dualHomQ_map, dualHom_id, (functor U).map_id]

/-- The duality of `𝒜/𝒰`: `⟨M⟩^* = ⟨M^*⟩` and `[f]^* = [f^*]`. -/
instance : DualCat (FiltQuot U) where
  dual M := (functor U).obj (dual M.as)
  dualHom f := dualHomQ U f
  dualHom_id := by
    rintro ⟨M⟩
    exact dualHomQ_id U M
  dualHom_comp := by
    rintro ⟨M⟩ ⟨N⟩ ⟨P⟩ f g
    obtain ⟨f, rfl⟩ := (functor U).map_surjective f
    obtain ⟨g, rfl⟩ := (functor U).map_surjective g
    rw [← Functor.map_comp, dualHomQ_map, dualHomQ_map, dualHomQ_map, dualHom_comp,
      Functor.map_comp]
  dualHom_add := by
    rintro ⟨M⟩ ⟨N⟩ f g
    obtain ⟨f, rfl⟩ := (functor U).map_surjective f
    obtain ⟨g, rfl⟩ := (functor U).map_surjective g
    rw [← Functor.map_add, dualHomQ_map, dualHomQ_map, dualHomQ_map, dualHom_add,
      Functor.map_add]
  dualHom_smul := by
    rintro ⟨M⟩ ⟨N⟩ c f
    obtain ⟨f, rfl⟩ := (functor U).map_surjective f
    rw [← Functor.map_smul, dualHomQ_map, dualHomQ_map, dualHom_smul, Functor.map_smul]
  dual_dual := by
    rintro ⟨M⟩
    show (functor U).obj (dual (dual M)) = (functor U).obj M
    rw [dual_dual]
  dualHom_dualHom := by
    rintro ⟨M⟩ ⟨N⟩ f
    obtain ⟨f, rfl⟩ := (functor U).map_surjective f
    rw [dualHomQ_map]
    show (functor U).map (dualHom (dualHom f)) = _
    rw [dualHom_dualHom, Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
  dualHom_zero := by
    rintro ⟨M⟩ ⟨N⟩
    rw [← (functor U).map_zero M N, dualHomQ_map, dualHom_zero, Functor.map_zero]
  dualHom_neg := by
    rintro ⟨M⟩ ⟨N⟩ f
    obtain ⟨f, rfl⟩ := (functor U).map_surjective f
    rw [← Functor.map_neg, dualHomQ_map, dualHomQ_map, dualHom_neg, Functor.map_neg]
  dualHom_sub := by
    rintro ⟨M⟩ ⟨N⟩ f g
    obtain ⟨f, rfl⟩ := (functor U).map_surjective f
    obtain ⟨g, rfl⟩ := (functor U).map_surjective g
    rw [← Functor.map_sub, dualHomQ_map, dualHomQ_map, dualHomQ_map, dualHom_sub,
      Functor.map_sub]
  dualHom_eqToHom := by
    rintro ⟨M⟩ _ rfl
    exact dualHomQ_id U M

lemma dual_def (M : FiltQuot U) : dual M = (functor U).obj (dual M.as) := rfl

lemma dualHom_map {M N : A} (g : M ⟶ N) :
    dualHom ((functor U).map g) = (functor U).map (dualHom g) := rfl

end FiltQuot

end HSP
