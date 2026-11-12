import Mathlib
import HilbertSmithPaper.LTheory.Base.Categories.DualSubcategory
import HilbertSmithPaper.LTheory.Base.Categories.Sums.DualBiproduct
import HilbertSmithPaper.LTheory.Bounded.Categories.KZeroStableEquality
import HilbertSmithPaper.LTheory.Localization.Decorations.DecoratedPredicate

/-!
# Decorated objects are closed under sums and duals

The decorated objects of `Kar(𝒜/𝒰)` contain a zero object, a sum of any two of them, and the
dual of each of them: `[q 0] = 0`, `[M ⊕ N] = [q(Q ⊕ Q')]`, and if `M ⊕ X ≅ q Q ⊕ X` then
`M^* ⊕ X^* ≅ q(Q^*) ⊕ X^*` since `q` is strict.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

open scoped ZeroObject

namespace HSP

open DualCat

universe v u

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
  preservesBinaryBiproducts_of_preservesBiproducts

section Helpers

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

omit [Preadditive C] [HasFiniteBiproducts C] in
private lemma cls_iso [Preadditive C] [HasFiniteBiproducts C] {P Q : Karoubi C} (e : P ≅ Q) :
    K0.cls P = K0.cls Q := by
  unfold K0.cls
  rw [K0.IsoClasses.mk_eq_mk_iff.mpr ⟨e⟩]

private lemma cls_biprod (P Q : Karoubi C) : K0.cls (P ⊞ Q) = K0.cls P + K0.cls Q := by
  simp only [K0.cls, ← K0.IsoClasses.mk_add, map_add]

variable [Linear ℚ C] [DualCat C]

/-- The dual of an isomorphism. -/
private def dualIsoOf {M N : C} (e : M ≅ N) : dual N ≅ dual M where
  hom := dualHom e.hom
  inv := dualHom e.inv
  hom_inv_id := by rw [← dualHom_comp, e.inv_hom_id, dualHom_id]
  inv_hom_id := by rw [← dualHom_comp, e.hom_inv_id, dualHom_id]

end Helpers

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A] (U : ObjectProperty A) [IsDualAdditive U]

/-- **Decorated objects are closed under sums and duals.** -/
instance IsDecorated.isDualAdditive : IsDualAdditive (IsDecorated U) where
  exists_zero := ⟨(FiltQuot.q U).kar.toFunctor.obj 0, ⟨0, rfl⟩,
    Functor.map_isZero _ (isZero_zero _)⟩
  exists_biprod := by
    rintro V W ⟨Q, hQ⟩ ⟨Q', hQ'⟩
    refine ⟨BinaryBiproduct.bicone V W, ⟨BinaryBiproduct.isBilimit V W⟩, Q ⊞ Q', ?_⟩
    change K0.cls (V ⊞ W) = _
    rw [cls_biprod, hQ, hQ', ← cls_biprod]
    exact cls_iso ((FiltQuot.q U).kar.toFunctor.mapBiprod Q Q').symm
  dual_mem := by
    rintro V ⟨Q, hQ⟩
    obtain ⟨X, ⟨e⟩⟩ := (K0.cls_eq_iff _ _).mp hQ
    refine ⟨dual Q, (K0.cls_eq_iff _ _).mpr ⟨dual X, ⟨?_⟩⟩⟩
    have s := (DualFunctor.kar_isStrict _ (FiltQuot.q_isStrict U) Q).fst
    have t : (toKaroubi (FiltQuot U)).obj (dual X) = dual ((toKaroubi (FiltQuot U)).obj X) :=
      Karoubi.ext rfl (by simp [Karoubi.dual_p, dualHom_id])
    exact biprod.mapIso (Iso.refl _) (eqToIso t) ≪≫ (dualBiprodIso _ _).symm ≪≫
      dualIsoOf e.symm ≪≫ dualBiprodIso _ _ ≪≫ biprod.mapIso (eqToIso s.symm) (eqToIso t.symm)

end HSP
