import HilbertSmithPaper.LTheory.Base.Categories.KaroubiDuality

/-!
# `K_0` of an idempotent completion

`K_0(Kar A)` is the Grothendieck group (Mathlib's `Algebra.GrothendieckAddGroup`) of the
commutative monoid `K0.IsoClasses (Karoubi A)` of isomorphism classes of objects of `Kar A`
(the quotient by Mathlib's `isIsomorphicSetoid`), with `[X] + [Y] = [X ⊞ Y]` and `0 = [0]`.
`K0.cls P` is the class `[P]`.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

open scoped ZeroObject

noncomputable section

namespace HSP

universe v u

namespace K0

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

/-- The isomorphism classes of objects of `C`. -/
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

/-- `K_0(Kar A)`: the Grothendieck group of the commutative monoid of isomorphism classes of
objects of `Kar A` under `⊕`. -/
abbrev K0 (A : Type u) [Category.{v} A] [Preadditive A] [HasFiniteBiproducts A] : Type (max u v) :=
  Algebra.GrothendieckAddGroup (K0.IsoClasses (Karoubi A))

namespace K0

variable {A : Type u} [Category.{v} A] [Preadditive A] [HasFiniteBiproducts A]

/-- The class `[P] ∈ K_0(Kar A)` of an object `P` of `Kar A`. -/
def cls (P : Karoubi A) : K0 A := Algebra.GrothendieckAddGroup.of (IsoClasses.mk P)

end K0

end HSP

end
