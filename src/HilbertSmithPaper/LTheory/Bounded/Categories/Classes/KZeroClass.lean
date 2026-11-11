import HilbertSmithPaper.LTheory.Bounded.Categories.KZero

/-!
# The class of an object in K_0

An object `P` of `Kar A` has a class `[P] ∈ K_0(Kar A)`, the image of its isomorphism class.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

open scoped ZeroObject

noncomputable section

namespace HSP

universe v u

namespace K0

variable {A : Type u} [Category.{v} A] [Preadditive A] [HasFiniteBiproducts A]

/-- **The class of an object in K_0.** The class `[P] ∈ K_0(Kar A)` of an object `P` of `Kar A`. -/
def cls (P : Karoubi A) : K0 A := Algebra.GrothendieckAddGroup.of (IsoClasses.mk P)

end K0

end HSP

end
