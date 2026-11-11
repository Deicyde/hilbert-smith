import HilbertSmithPaper.LTheory.Base.Categories.DualityCategory

/-!
# Additive subcategory closed under duality

A full subcategory `𝒰 ⊂ 𝒜` of a duality category is given by a predicate `U : ObjectProperty A`
on objects. It is *additive and closed under duality* if it contains a zero object, contains a
sum of any two of its objects, and contains `V^*` with `V`.

Encoding of "contains a sum": some biproduct bicone of `V` and `W` (a bilimit) has its cone point
in `U`. This does not refer to the chosen biproduct `V ⊞ W` of `𝒜`, which is determined only up
to isomorphism, and it does not ask `U` to be closed under isomorphism (the quotient support
filtrations of the paper are not).
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v u

/-- A predicate `U` on the objects of a duality category is a *full additive subcategory closed
under duality* if it contains a zero object, contains a sum (a biproduct of the two objects) of
any two of its objects, and contains `V^*` whenever it contains `V`. -/
class IsDualAdditive {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A]
    [HasFiniteBiproducts A] [DualCat A] (U : ObjectProperty A) : Prop where
  /-- `U` contains a zero object. -/
  exists_zero : ∃ Z : A, U Z ∧ IsZero Z
  /-- `U` contains a sum of any two of its objects. -/
  exists_biprod {V W : A} : U V → U W →
    ∃ c : BinaryBicone V W, Nonempty c.IsBilimit ∧ U c.pt
  /-- `U` is closed under the duality. -/
  dual_mem {V : A} : U V → U (dual V)

end HSP
