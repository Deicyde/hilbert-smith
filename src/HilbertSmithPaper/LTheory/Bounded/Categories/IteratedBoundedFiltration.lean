import HilbertSmithPaper.LTheory.Bounded.Categories.BoundedKaroubiFiltration
import HilbertSmithPaper.LTheory.Bounded.Categories.IteratedBoundedCategory

/-!
# Iterated bounded filtrations

For an involution-invariant Karoubi filtration of `A` by `U`, `C_{ℤ^j}U ⊂ C_{ℤ^j}A` is one for
every `j`. `Bounded.subPow U j` is `C_{ℤ^j}U`: `U` for `j = 0` and `Bounded.sub` of the previous
level otherwise; it is a full additive subcategory closed under duality (instance, by induction),
and `Bounded.powKaroubiFiltration F j` is the filtration, by induction: `F` for `j = 0` and the
bounded Karoubi filtration of the previous level otherwise.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace HSP

universe v u

namespace Bounded

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A] (U : ObjectProperty A)

/-- `C_{ℤ^j}U ⊂ C_{ℤ^j}A`: `U` for `j = 0`, and `C_ℤ` of the previous level otherwise. -/
def subPow : ∀ j : ℕ, ObjectProperty (BoundedPow A j)
  | 0 => U
  | j + 1 => sub (subPow j)

/-- `C_{ℤ^j}U` is a full additive subcategory closed under duality. -/
instance isDualAdditive_subPow [IsDualAdditive U] : ∀ j : ℕ, IsDualAdditive (subPow U j)
  | 0 => ‹IsDualAdditive U›
  | j + 1 => @isDualAdditive_sub (BoundedPow A j) _ _ _ _ _ (subPow U j)
    (isDualAdditive_subPow j)

variable {U}

/-- **Iterated bounded filtrations.** For an involution-invariant Karoubi filtration `F` of `A`
by `U` and every `j`, `C_{ℤ^j}U ⊂ C_{ℤ^j}A` is an involution-invariant Karoubi filtration. -/
def powKaroubiFiltration [IsDualAdditive U] (F : KaroubiFiltration U) :
    ∀ j : ℕ, KaroubiFiltration (subPow U j)
  | 0 => F
  | j + 1 => @karoubiFiltration (BoundedPow A j) _ _ _ _ _ (subPow U j)
    (isDualAdditive_subPow U j) (powKaroubiFiltration F j)

end Bounded

end HSP

end
