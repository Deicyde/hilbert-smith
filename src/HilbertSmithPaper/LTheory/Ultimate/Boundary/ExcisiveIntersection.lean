import HilbertSmithPaper.LTheory.Base.Categories.DualSubcategory

/-!
# Intersection of full subcategories

For full subcategories `𝒰_A, 𝒰_B ⊂ 𝒜`, the intersection `𝒰_A ∩ 𝒰_B` is the full subcategory of
`𝒰_A` of the objects that lie in `𝒰_B`.

## Encoding

`ExcisivePair.inter UA UB` (the declaration of the article) is the property `fun V => UB V.obj`
of objects of `UA.FullSubcategory`.
-/

open CategoryTheory

namespace HSP

universe v u

variable {A : Type u} [Category.{v} A]

namespace ExcisivePair

/-- The intersection `𝒰_Y = 𝒰_A ∩ 𝒰_B`, as a property of objects of `𝒰_A`. -/
abbrev inter (UA UB : ObjectProperty A) : ObjectProperty UA.FullSubcategory :=
  fun V => UB V.obj

end ExcisivePair

end HSP
