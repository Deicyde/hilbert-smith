import HilbertSmithPaper.LTheory.Bounded.Categories.BoundedKaroubiFiltration
import HilbertSmithPaper.LTheory.Bounded.Categories.IteratedBoundedCategory
import HilbertSmithPaper.LTheory.Bounded.Categories.IteratedBoundedSub
import HilbertSmithPaper.LTheory.Bounded.Categories.IteratedBoundedSubAdditive

/-!
# Iterated bounded filtrations

For an involution-invariant Karoubi filtration of `A` by `U`, `C_{ℤ^j}U ⊂ C_{ℤ^j}A` is one for
every `j`, with `C_{ℤ^j}U` the iterated bounded subcategory `Bounded.subPow U j`.
`Bounded.powKaroubiFiltration F j` is the filtration, by induction: `F` for `j = 0` and the
bounded Karoubi filtration of the previous level otherwise.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace HSP

universe v u

namespace Bounded

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A] (U : ObjectProperty A)

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
