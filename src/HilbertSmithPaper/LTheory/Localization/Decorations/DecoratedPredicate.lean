import Mathlib
import HilbertSmithPaper.LTheory.Base.Categories.FiltrationQuotient
import HilbertSmithPaper.LTheory.Base.Categories.KaroubiFunctor
import HilbertSmithPaper.LTheory.Base.Categories.KaroubiDuality
import HilbertSmithPaper.LTheory.Bounded.Categories.KZero
import HilbertSmithPaper.LTheory.Base.Categories.QuotientDualityFunctor
import HilbertSmithPaper.LTheory.Bounded.Categories.Classes.KZeroClass

/-!
# Decorated objects of the completed quotient

For a dual-closed full additive subcategory `𝒰 ⊂ 𝒜` with quotient `q : 𝒜 → 𝒜/𝒰` (and its
completion `Kar q`), an object `M` of `Kar(𝒜/𝒰)` is *decorated* if `[M] = [q Q]` in
`K_0(Kar(𝒜/𝒰))` for some object `Q` of `Kar 𝒜`.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

namespace HSP

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A] (U : ObjectProperty A) [IsDualAdditive U]

/-- **Decorated objects of the completed quotient.** An object `M` of `Kar(𝒜/𝒰)` is
*decorated* if `[M] = [q Q]` in `K_0(Kar(𝒜/𝒰))` for some object `Q` of `Kar 𝒜`. -/
def IsDecorated : ObjectProperty (Karoubi (FiltQuot U)) := fun M =>
  ∃ Q : Karoubi A, K0.cls M = K0.cls ((FiltQuot.q U).kar.toFunctor.obj Q)

end HSP
