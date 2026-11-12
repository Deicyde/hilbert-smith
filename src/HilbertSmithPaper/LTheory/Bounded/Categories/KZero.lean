import HilbertSmithPaper.LTheory.Base.Categories.KaroubiDuality
import HilbertSmithPaper.LTheory.Bounded.Categories.Classes.IsoClasses

/-!
# `K_0` of an idempotent completion

`K_0(Kar A)` is the Grothendieck group (Mathlib's `Algebra.GrothendieckAddGroup`) of the
commutative monoid `K0.IsoClasses (Karoubi A)` of isomorphism classes of objects of `Kar A`
(the quotient by Mathlib's `isIsomorphicSetoid`), with `[X] + [Y] = [X ⊞ Y]` and `0 = [0]`.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

open scoped ZeroObject

noncomputable section

namespace HSP

universe v u

/-- `K_0(Kar A)`: the Grothendieck group of the commutative monoid of isomorphism classes of
objects of `Kar A` under `⊕`. -/
abbrev K0 (A : Type u) [Category.{v} A] [Preadditive A] [HasFiniteBiproducts A] : Type (max u v) :=
  Algebra.GrothendieckAddGroup (K0.IsoClasses (Karoubi A))

end HSP

end
