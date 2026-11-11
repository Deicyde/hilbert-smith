import HilbertSmithPaper.LTheory.Base.Categories.DualityFunctor
import HilbertSmithPaper.LTheory.Base.Categories.DualAdditiveSubcategory

/-!
# Quotient by a subcategory

For a full additive subcategory `𝒰 ⊂ 𝒜` closed under duality (`HSP.IsDualAdditive U`), the maps
factoring through an object of `𝒰` form a ℚ-linear ideal `I_𝒰` closed under `*`
(`FiltQuot.ideal`). The quotient `𝒜/𝒰` is Mathlib's `CategoryTheory.Quotient` by the relation
`f ~ g ⇔ f - g ∈ I_𝒰` (`FiltQuot.rel`), a congruence compatible with sums and scalars, so it
carries `Quotient.preadditive` and `Quotient.linear`. Its finite biproducts are the images of
those of `𝒜` under the additive quotient functor, and its duality is `⟨M⟩^* = ⟨M^*⟩`,
`[f]^* = [f^*]`. The quotient functor `q` (`FiltQuot.q`) is a strict duality functor:
`ξ_M` is the identity of `⟨M^*⟩`.

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

/-- The ideal `I_𝒰(M, N)`: the maps `M ⟶ N` that factor through an object of `𝒰`. -/
def ideal (U : ObjectProperty A) {M N : A} (f : M ⟶ N) : Prop :=
  ∃ V : A, U V ∧ ∃ (a : M ⟶ V) (b : V ⟶ N), f = a ≫ b

/-- The relation `f ~ g ⇔ f - g ∈ I_𝒰` whose quotient is `𝒜/𝒰`. -/
def rel (U : ObjectProperty A) : HomRel A := fun _ _ f g => ideal U (f - g)

variable {U : ObjectProperty A}

lemma ideal_zero [IsDualAdditive U] {M N : A} : ideal U (0 : M ⟶ N) := by
  obtain ⟨Z, hZ, -⟩ := IsDualAdditive.exists_zero (U := U)
  exact ⟨Z, hZ, 0, 0, by simp⟩

lemma ideal_add [IsDualAdditive U] {M N : A} {f g : M ⟶ N} (hf : ideal U f) (hg : ideal U g) :
    ideal U (f + g) := by
  obtain ⟨V, hV, a, b, rfl⟩ := hf
  obtain ⟨W, hW, c, d, rfl⟩ := hg
  obtain ⟨P, -, hP⟩ := IsDualAdditive.exists_biprod hV hW
  refine ⟨P.pt, hP, a ≫ P.inl + c ≫ P.inr, P.fst ≫ b + P.snd ≫ d, ?_⟩
  simp

omit [Linear ℚ A] [HasFiniteBiproducts A] [DualCat A] in
lemma ideal_neg {M N : A} {f : M ⟶ N} (hf : ideal U f) : ideal U (-f) := by
  obtain ⟨V, hV, a, b, rfl⟩ := hf
  exact ⟨V, hV, -a, b, by simp⟩

omit [HasFiniteBiproducts A] [DualCat A] in
lemma ideal_smul {M N : A} (c : ℚ) {f : M ⟶ N} (hf : ideal U f) : ideal U (c • f) := by
  obtain ⟨V, hV, a, b, rfl⟩ := hf
  exact ⟨V, hV, c • a, b, by simp⟩

omit [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A] [DualCat A] in
lemma ideal_comp_left {L M N : A} (h : L ⟶ M) {f : M ⟶ N} (hf : ideal U f) :
    ideal U (h ≫ f) := by
  obtain ⟨V, hV, a, b, rfl⟩ := hf
  exact ⟨V, hV, h ≫ a, b, by simp⟩

omit [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A] [DualCat A] in
lemma ideal_comp_right {M N P : A} {f : M ⟶ N} (hf : ideal U f) (h : N ⟶ P) :
    ideal U (f ≫ h) := by
  obtain ⟨V, hV, a, b, rfl⟩ := hf
  exact ⟨V, hV, a, b ≫ h, by simp⟩

lemma ideal_dual [IsDualAdditive U] {M N : A} {f : M ⟶ N} (hf : ideal U f) :
    ideal U (dualHom f) := by
  obtain ⟨V, hV, a, b, rfl⟩ := hf
  exact ⟨dual V, IsDualAdditive.dual_mem hV, dualHom b, dualHom a, by simp⟩

instance [IsDualAdditive U] : Congruence (rel U) where
  equivalence :=
    { refl _ := by simpa [rel] using ideal_zero
      symm {f g} h := by simpa [rel] using ideal_neg h
      trans {f g k} h₁ h₂ := by simpa [rel] using ideal_add h₁ h₂ }
  comp_left := by
    intro _ _ _ h _ _ hfg
    simpa [rel, Preadditive.comp_sub] using ideal_comp_left h hfg
  comp_right := by
    intro _ _ _ _ _ h hfg
    simpa [rel, Preadditive.sub_comp] using ideal_comp_right hfg h

private lemma rel_add [IsDualAdditive U] ⦃M N : A⦄ (f₁ f₂ g₁ g₂ : M ⟶ N) (h₁ : rel U f₁ f₂)
    (h₂ : rel U g₁ g₂) : rel U (f₁ + g₁) (f₂ + g₂) := by
  have := ideal_add h₁ h₂
  unfold rel
  convert this using 1
  abel

omit [HasFiniteBiproducts A] [DualCat A] in
private lemma rel_smul (c : ℚ) ⦃M N : A⦄ (f₁ f₂ : M ⟶ N) (h : rel U f₁ f₂) :
    rel U (c • f₁) (c • f₂) := by
  simpa [rel, smul_sub] using ideal_smul c h

end FiltQuot

/-- The *quotient* `𝒜/𝒰` of a duality category by a full additive subcategory closed under
duality: the objects of `𝒜`, with `Hom(M, N) / I_𝒰(M, N)`. It is a duality category, and the
quotient functor `FiltQuot.q` is a strict duality functor. -/
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

omit [Linear ℚ A] [HasFiniteBiproducts A] [DualCat A] [IsDualAdditive U] in
lemma functor_map_surjective {M N : A} (f : (functor U).obj M ⟶ (functor U).obj N) :
    ∃ g : M ⟶ N, (functor U).map g = f :=
  (functor U).map_surjective f

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
    exact ideal_dual h

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
    obtain ⟨f, rfl⟩ := functor_map_surjective U f
    obtain ⟨g, rfl⟩ := functor_map_surjective U g
    rw [← Functor.map_comp, dualHomQ_map, dualHomQ_map, dualHomQ_map, dualHom_comp,
      Functor.map_comp]
  dualHom_add := by
    rintro ⟨M⟩ ⟨N⟩ f g
    obtain ⟨f, rfl⟩ := functor_map_surjective U f
    obtain ⟨g, rfl⟩ := functor_map_surjective U g
    rw [← Functor.map_add, dualHomQ_map, dualHomQ_map, dualHomQ_map, dualHom_add,
      Functor.map_add]
  dualHom_smul := by
    rintro ⟨M⟩ ⟨N⟩ c f
    obtain ⟨f, rfl⟩ := functor_map_surjective U f
    rw [← Functor.map_smul, dualHomQ_map, dualHomQ_map, dualHom_smul, Functor.map_smul]
  dual_dual := by
    rintro ⟨M⟩
    show (functor U).obj (dual (dual M)) = (functor U).obj M
    rw [dual_dual]
  dualHom_dualHom := by
    rintro ⟨M⟩ ⟨N⟩ f
    obtain ⟨f, rfl⟩ := functor_map_surjective U f
    rw [dualHomQ_map]
    show (functor U).map (dualHom (dualHom f)) = _
    rw [dualHom_dualHom, Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
  dualHom_zero := by
    rintro ⟨M⟩ ⟨N⟩
    rw [← (functor U).map_zero M N, dualHomQ_map, dualHom_zero, Functor.map_zero]
  dualHom_neg := by
    rintro ⟨M⟩ ⟨N⟩ f
    obtain ⟨f, rfl⟩ := functor_map_surjective U f
    rw [← Functor.map_neg, dualHomQ_map, dualHomQ_map, dualHom_neg, Functor.map_neg]
  dualHom_sub := by
    rintro ⟨M⟩ ⟨N⟩ f g
    obtain ⟨f, rfl⟩ := functor_map_surjective U f
    obtain ⟨g, rfl⟩ := functor_map_surjective U g
    rw [← Functor.map_sub, dualHomQ_map, dualHomQ_map, dualHomQ_map, dualHom_sub,
      Functor.map_sub]
  dualHom_eqToHom := by
    rintro ⟨M⟩ _ rfl
    exact dualHomQ_id U M

lemma dual_def (M : FiltQuot U) : dual M = (functor U).obj (dual M.as) := rfl

lemma dualHom_map {M N : A} (g : M ⟶ N) :
    dualHom ((functor U).map g) = (functor U).map (dualHom g) := rfl

/-- The quotient functor `q : 𝒜 → 𝒜/𝒰` as a duality functor, with `ξ_M` the identity of
`⟨M^*⟩`. -/
def q : DualFunctor A (FiltQuot U) where
  toFunctor := functor U
  ξ M := Iso.refl _
  ξ_natural f := by simp [dualHom_map]
  ξ_dual M := by
    simp only [Iso.refl_hom, dualHom_id, eqToHom_refl, Category.comp_id]
    rfl

/-- The quotient functor is a strict duality functor. -/
lemma q_isStrict : (q U).IsStrict := fun _ => ⟨rfl, rfl⟩

end FiltQuot

end HSP
