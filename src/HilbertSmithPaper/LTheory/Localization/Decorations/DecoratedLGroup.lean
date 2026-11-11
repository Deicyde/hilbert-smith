import Mathlib
import HilbertSmithPaper.LTheory.Base.Groups.LGroup
import HilbertSmithPaper.LTheory.Localization.Decorations.DecoratedObject

/-!
# Decorated quotient L-group

For a dual-closed full additive subcategory `𝒰 ⊂ 𝒜`,
`L^{im}_k(𝒜/𝒰) = L_k(Dec(𝒜/𝒰))`, the L-group of the duality category of decorated objects:
cobordism classes of strict `k`-dimensional symmetric Poincaré complexes whose chain objects are
decorated.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v u

/-- **Decorated quotient L-group.** `L^{im}_k(𝒜/𝒰) = L_k(Dec(𝒜/𝒰))`. -/
noncomputable abbrev LIm {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A]
    [HasFiniteBiproducts A] [DualCat A] (U : ObjectProperty A) [IsDualAdditive U] (k : ℤ) :
    Type (max u v) :=
  LGroup (Dec U) k

end HSP
