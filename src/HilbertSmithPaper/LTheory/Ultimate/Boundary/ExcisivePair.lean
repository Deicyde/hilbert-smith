import HilbertSmithPaper.LTheory.Base.Categories.KaroubiFiltration
import HilbertSmithPaper.LTheory.Base.Categories.FiltrationQuotient
import HilbertSmithPaper.LTheory.Base.Categories.UnitaryIsomorphism
import HilbertSmithPaper.LTheory.Base.Categories.WholeFiltration
import HilbertSmithPaper.LTheory.Base.Categories.DualSubcategory
import HilbertSmithPaper.LTheory.Ultimate.Boundary.ExcisiveIntersection

/-!
# Excisive pair of filtrations

An excisive pair in a duality category `𝒜` consists of involution-invariant Karoubi filtrations
`𝒰_A, 𝒰_B ⊂ 𝒜` such that `𝒰_Y = 𝒰_A ∩ 𝒰_B` is an involution-invariant Karoubi filtration of
`𝒰_A`, a duality functor `r : 𝒜/𝒰_B → 𝒰_A/𝒰_Y`, and unitary natural isomorphisms
`id ≅ r ∘ e`, `e ∘ r ≅ id`, where `e : 𝒰_A/𝒰_Y → 𝒜/𝒰_B` is the strict duality functor that is
the identity on objects and sends the class of a morphism modulo `𝒰_Y` to its class modulo
`𝒰_B` (`ExcisivePair.e`).

Lean: `𝒰_A` is the duality category `UA.FullSubcategory` (`HSP.instDualCatFullSubcategory`),
and `𝒰_Y` is the intersection `ExcisivePair.inter UA UB`, a property of objects of `𝒰_A`. The closure of `𝒰_Y` under zero objects,
sums and duals inside `𝒰_A` is asked as a hypothesis (it is part of "`𝒰_Y` is a filtration of
`𝒰_A`").
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]

namespace ExcisivePair

variable (UA UB : ObjectProperty A) [IsDualAdditive UA] [IsDualAdditive UB]
  [IsDualAdditive (inter UA UB)]

omit [IsDualAdditive UA] [IsDualAdditive (inter UA UB)] in
private lemma lift_compat (x y : UA.FullSubcategory) (f₁ f₂ : x ⟶ y)
    (h : FiltQuot.rel (inter UA UB) f₁ f₂) :
    (UA.ι ⋙ FiltQuot.functor UB).map f₁ = (UA.ι ⋙ FiltQuot.functor UB).map f₂ := by
  obtain ⟨V, hV, a, b, hab⟩ := h
  simp only [Functor.comp_map, ObjectProperty.ι_map]
  rw [FiltQuot.functor_map_eq_iff]
  exact ⟨V.obj, hV, a.hom, b.hom, congrArg InducedCategory.Hom.hom hab⟩

/-- The underlying functor of `e`: identity on objects, `[f]_{𝒰_Y} ↦ [f]_{𝒰_B}`. -/
abbrev eFunctor : FiltQuot (inter UA UB) ⥤ FiltQuot UB :=
  CategoryTheory.Quotient.lift (FiltQuot.rel (inter UA UB)) (UA.ι ⋙ FiltQuot.functor UB)
    (lift_compat UA UB)

instance : (eFunctor UA UB).Additive where
  map_add {X Y f g} := by
    obtain ⟨f, rfl⟩ := FiltQuot.functor_map_surjective (inter UA UB) f
    obtain ⟨g, rfl⟩ := FiltQuot.functor_map_surjective (inter UA UB) g
    rw [← Functor.map_add, CategoryTheory.Quotient.lift_map_functor_map,
      CategoryTheory.Quotient.lift_map_functor_map,
      CategoryTheory.Quotient.lift_map_functor_map, Functor.map_add]

instance : (eFunctor UA UB).Linear ℚ where
  map_smul {X Y} f c := by
    obtain ⟨f, rfl⟩ := FiltQuot.functor_map_surjective (inter UA UB) f
    rw [← Functor.map_smul, CategoryTheory.Quotient.lift_map_functor_map,
      CategoryTheory.Quotient.lift_map_functor_map,
      Functor.map_smul]

/-- The strict duality functor `e : 𝒰_A/𝒰_Y → 𝒜/𝒰_B`, the identity on objects, sending the class
of a morphism modulo `𝒰_Y` to its class modulo `𝒰_B`. -/
def e : DualFunctor (FiltQuot (inter UA UB)) (FiltQuot UB) where
  toFunctor := eFunctor UA UB
  ξ M := Iso.refl _
  ξ_natural {M N} f := by
    obtain ⟨f, rfl⟩ := FiltQuot.functor_map_surjective (inter UA UB) f
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rw [FiltQuot.dualHom_map, CategoryTheory.Quotient.lift_map_functor_map,
      CategoryTheory.Quotient.lift_map_functor_map]
    rfl
  ξ_dual M := by
    simp only [Iso.refl_hom, dualHom_id, eqToHom_refl, Category.comp_id]
    rfl

end ExcisivePair

/-- An *excisive pair* of involution-invariant Karoubi filtrations `𝒰_A, 𝒰_B ⊂ 𝒜`, with
`𝒰_Y = 𝒰_A ∩ 𝒰_B` a filtration of `𝒰_A`, a duality functor `r : 𝒜/𝒰_B → 𝒰_A/𝒰_Y`, and unitary
natural isomorphisms `id ≅ r ∘ e` and `e ∘ r ≅ id`. -/
structure ExcisivePair (A : Type u) [Category.{v} A] [Preadditive A] [Linear ℚ A]
    [HasFiniteBiproducts A] [DualCat A] where
  /-- The subcategory `𝒰_A`. -/
  UA : ObjectProperty A
  /-- The subcategory `𝒰_B`. -/
  UB : ObjectProperty A
  [isDualAdditive_A : IsDualAdditive UA]
  [isDualAdditive_B : IsDualAdditive UB]
  /-- `𝒰_A ⊂ 𝒜` is an involution-invariant Karoubi filtration. -/
  filtA : KaroubiFiltration UA
  /-- `𝒰_B ⊂ 𝒜` is an involution-invariant Karoubi filtration. -/
  filtB : KaroubiFiltration UB
  [isDualAdditive_Y : IsDualAdditive (ExcisivePair.inter UA UB)]
  /-- `𝒰_Y ⊂ 𝒰_A` is an involution-invariant Karoubi filtration. -/
  filtY : KaroubiFiltration (ExcisivePair.inter UA UB)
  /-- The duality functor `r : 𝒜/𝒰_B → 𝒰_A/𝒰_Y`. -/
  r : DualFunctor (FiltQuot UB) (FiltQuot (ExcisivePair.inter UA UB))
  /-- A unitary natural isomorphism `id ≅ r ∘ e`. -/
  unit : DualFunctor.UnitaryIso (DualFunctor.id _) ((ExcisivePair.e UA UB).comp r)
  /-- A unitary natural isomorphism `e ∘ r ≅ id`. -/
  counit : DualFunctor.UnitaryIso (r.comp (ExcisivePair.e UA UB)) (DualFunctor.id _)

attribute [instance] ExcisivePair.isDualAdditive_A ExcisivePair.isDualAdditive_B
  ExcisivePair.isDualAdditive_Y


/-! Non-vacuity: based vector spaces with `𝒰_A = 𝒰_B` the whole filtration. Both quotients have
only zero maps; `r` is the identity on objects. -/

section NonVacuity

/-- In a quotient by a subcategory containing every object, any two parallel maps agree. -/
private lemma filtQuot_hom_eq {B : Type*} [Category B] [Preadditive B] [Linear ℚ B]
    [HasFiniteBiproducts B] [DualCat B] {U : ObjectProperty B} [IsDualAdditive U]
    (hU : ∀ X, U X) {M N : FiltQuot U} (f g : M ⟶ N) : f = g := by
  obtain ⟨M⟩ := M
  obtain ⟨N⟩ := N
  obtain ⟨f, rfl⟩ := FiltQuot.functor_map_surjective (U := U) f
  obtain ⟨g, rfl⟩ := FiltQuot.functor_map_surjective (U := U) g
  rw [FiltQuot.functor_map_eq_iff]
  exact ⟨M, hU M, 𝟙 M, f - g, (Category.id_comp _).symm⟩

private abbrev UY : ObjectProperty (⊤ : ObjectProperty FreeQ).FullSubcategory :=
  ExcisivePair.inter ⊤ ⊤

private instance : IsDualAdditive UY :=
  isDualAdditive_top (⊤ : ObjectProperty FreeQ).FullSubcategory

private lemma hom_eq_A {M N : FiltQuot (⊤ : ObjectProperty FreeQ)} (f g : M ⟶ N) : f = g :=
  filtQuot_hom_eq (U := ⊤) (fun _ => trivial) f g

private lemma hom_eq_Y {M N : FiltQuot UY} (f g : M ⟶ N) : f = g :=
  filtQuot_hom_eq (U := UY) (fun _ => trivial) f g

/-- The functor `𝒜/𝒰_B ⥤ 𝒰_A/𝒰_Y`, the identity on objects. -/
private noncomputable def rFunctor : FiltQuot (⊤ : ObjectProperty FreeQ) ⥤ FiltQuot UY where
  obj M := (FiltQuot.functor UY).obj ⟨M.as, trivial⟩
  map _ := 0
  map_id _ := hom_eq_Y _ _
  map_comp _ _ := hom_eq_Y _ _

private instance : rFunctor.Additive where
  map_add := hom_eq_Y _ _

private instance : rFunctor.Linear ℚ where
  map_smul _ _ := hom_eq_Y _ _

/-- The duality functor `r`, with `ξ` the zero isomorphism. -/
private noncomputable def rTop : DualFunctor (FiltQuot (⊤ : ObjectProperty FreeQ)) (FiltQuot UY) where
  toFunctor := rFunctor
  ξ _ := ⟨0, 0, hom_eq_Y _ _, hom_eq_Y _ _⟩
  ξ_natural _ := hom_eq_Y _ _
  ξ_dual _ := hom_eq_Y _ _

/-- The excisive pair of based vector spaces with `𝒰_A = 𝒰_B` the whole filtration. -/
private noncomputable def excisivePairTop : ExcisivePair FreeQ where
  UA := ⊤
  UB := ⊤
  filtA := KaroubiFiltration.top FreeQ
  filtB := KaroubiFiltration.top FreeQ
  filtY := KaroubiFiltration.top (⊤ : ObjectProperty FreeQ).FullSubcategory
  r := rTop
  unit :=
    { iso := NatIso.ofComponents (fun _ => ⟨0, 0, hom_eq_Y _ _, hom_eq_Y _ _⟩)
        fun _ => hom_eq_Y _ _
      unitary _ := hom_eq_Y _ _ }
  counit :=
    { iso := NatIso.ofComponents (fun _ => ⟨0, 0, hom_eq_A _ _, hom_eq_A _ _⟩)
        fun _ => hom_eq_A _ _
      unitary _ := hom_eq_A _ _ }

end NonVacuity

end HSP
