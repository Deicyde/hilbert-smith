import HilbertSmithPaper.LTheory.Base.Groups.LGroup
import HilbertSmithPaper.LTheory.Base.Categories.KaroubiDuality

/-!
# The projective L-group

The projective L-group of a duality category `A` is `L^p_k(A) = L_k(Kar A)`, the L-group of its
idempotent completion with the induced duality.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

namespace HSP

universe v u

/-- **The projective L-group.** `L^p_k(A) = L_k(Kar A)`. -/
abbrev Lp (A : Type u) [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
    [DualCat A] (k : ℤ) : Type (max u v) :=
  LGroup (Karoubi A) k

end HSP
