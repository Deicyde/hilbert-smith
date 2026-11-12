import Mathlib
import HilbertSmithPaper.LTheory.Localization.Decorations.DecoratedClosure

/-!
# Decorated objects

For a dual-closed full additive subcategory `𝒰 ⊂ 𝒜`, the full subcategory `Dec(𝒜/𝒰)` of decorated
objects of `Kar(𝒜/𝒰)`, with the duality of `Kar(𝒜/𝒰)`, is a duality category.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

namespace HSP

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A] (U : ObjectProperty A) [IsDualAdditive U]

/-- **Decorated objects.** The full subcategory `Dec(𝒜/𝒰) ⊂ Kar(𝒜/𝒰)` of decorated objects,
with the duality of `Kar(𝒜/𝒰)`, a duality category. -/
abbrev Dec : Type _ := (IsDecorated U).FullSubcategory

end HSP
