import Mathlib

/-!
# Isomorphism classes of objects

For a preadditive category `C` with finite biproducts, the isomorphism classes of objects form
a commutative monoid under `[X] + [Y] = [X ⊞ Y]`, with `0 = [0]`.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

open scoped ZeroObject

noncomputable section

namespace HSP

universe v u

namespace K0

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

/-- **Isomorphism classes of objects.** The isomorphism classes of objects of `C`. -/
def IsoClasses : Type u := Quotient (isIsomorphicSetoid C)

namespace IsoClasses

variable {C}

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

/-- The class of an object. -/
def mk (X : C) : IsoClasses C := Quotient.mk _ X

omit [Preadditive C] [HasFiniteBiproducts C] in
lemma mk_eq_mk_iff {X Y : C} : mk X = mk Y ↔ Nonempty (X ≅ Y) := Quotient.eq (r := _)

instance : Add (IsoClasses C) :=
  ⟨Quotient.map₂ (fun X Y => X ⊞ Y) fun _ _ ⟨e⟩ _ _ ⟨f⟩ => ⟨biprod.mapIso e f⟩⟩

instance : Zero (IsoClasses C) := ⟨mk 0⟩

lemma mk_add (X Y : C) : mk X + mk Y = mk (X ⊞ Y) := rfl

/-- The commutative monoid of isomorphism classes under `⊕`. -/
instance : AddCommMonoid (IsoClasses C) where
  add_assoc := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩
    exact Quotient.sound ⟨biprod.associator X Y Z⟩
  zero_add := by
    rintro ⟨X⟩
    exact Quotient.sound ⟨(isoZeroBiprod (isZero_zero C)).symm⟩
  add_zero := by
    rintro ⟨X⟩
    exact Quotient.sound ⟨(isoBiprodZero (isZero_zero C)).symm⟩
  add_comm := by
    rintro ⟨X⟩ ⟨Y⟩
    exact Quotient.sound ⟨biprod.braiding X Y⟩
  nsmul := nsmulRec

end IsoClasses

end K0

end HSP

end
