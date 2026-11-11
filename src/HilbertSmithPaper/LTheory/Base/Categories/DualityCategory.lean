import Mathlib

/-!
# Small ℚ-linear category with strict duality

A duality category is a ℚ-linear additive category (preadditive, ℚ-linear, with finite
biproducts) together with a ℚ-linear contravariant functor `M ↦ M^*`, `f ↦ f^*`, which is an
involution on the nose: `M^** = M` and `f^** = f`. The second equation is stated with the
transports along the first, since `f^**` and `f` have equal but not definitionally equal types.

Smallness is automatic here: the objects form a type and every hom-set is a type.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v u

/-- A *duality category*: a ℚ-linear additive category `C` with a ℚ-linear contravariant
functor `dual` (written `M^*`, `f^*`) such that `M^** = M` and `f^** = f` on the nose. -/
class DualCat (C : Type u) [Category.{v} C] [Preadditive C] [Linear ℚ C]
    [HasFiniteBiproducts C] where
  /-- The dual object `M^*`. -/
  dual : C → C
  /-- The dual morphism `f^* : N^* ⟶ M^*` of `f : M ⟶ N`. -/
  dualHom {M N : C} : (M ⟶ N) → (dual N ⟶ dual M)
  dualHom_id (M : C) : dualHom (𝟙 M) = 𝟙 (dual M)
  dualHom_comp {M N P : C} (f : M ⟶ N) (g : N ⟶ P) :
    dualHom (f ≫ g) = dualHom g ≫ dualHom f
  dualHom_add {M N : C} (f g : M ⟶ N) : dualHom (f + g) = dualHom f + dualHom g
  dualHom_smul {M N : C} (c : ℚ) (f : M ⟶ N) : dualHom (c • f) = c • dualHom f
  dual_dual (M : C) : dual (dual M) = M
  dualHom_dualHom {M N : C} (f : M ⟶ N) :
    dualHom (dualHom f) = eqToHom (dual_dual M) ≫ f ≫ eqToHom (dual_dual N).symm
  /-- Derived (default proof): the dual of zero is zero. -/
  dualHom_zero {M N : C} : dualHom (0 : M ⟶ N) = 0 := by
    intro M N; simpa using dualHom_smul (0 : ℚ) (0 : M ⟶ N)
  /-- Derived (default proof): duality commutes with negation. -/
  dualHom_neg {M N : C} (f : M ⟶ N) : dualHom (-f) = -dualHom f := by
    intro M N f; simpa using dualHom_smul (-1 : ℚ) f
  /-- Derived (default proof): duality commutes with subtraction. -/
  dualHom_sub {M N : C} (f g : M ⟶ N) : dualHom (f - g) = dualHom f - dualHom g := by
    intro M N f g
    rw [sub_eq_add_neg, dualHom_add, sub_eq_add_neg]
    simpa using congrArg (dualHom f + ·) (dualHom_smul (-1 : ℚ) g)
  /-- Derived (default proof): duality of a transport is the reverse transport. -/
  dualHom_eqToHom {M N : C} (h : M = N) :
      dualHom (eqToHom h) = eqToHom (congrArg dual h).symm := by
    intro M N h; subst h; simpa using dualHom_id M

namespace DualCat

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℚ C] [HasFiniteBiproducts C]
  [DualCat C]

attribute [simp] dualHom_id dualHom_comp dualHom_add dualHom_smul dual_dual

attribute [simp] dualHom_zero dualHom_neg dualHom_sub dualHom_eqToHom

end DualCat

end HSP
