import HilbertSmithPaper.Categories.Supports.SupportDualAdditive
import HilbertSmithPaper.LTheory.Base.Categories.DualSubcategory

/-!
# Support subcategory inside a support subcategory

For `S, S' ⊆ X`, `𝒜_{S'} ⊂ 𝒜_S` (`HSP.suppIn S S'`) is the predicate "`S'`-supported" on the objects
of the duality category `𝒜_S = (supp S).FullSubcategory`.
-/

open CategoryTheory

namespace HSP

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

/-- `𝒜_{S'} ⊂ 𝒜_S`: the `S'`-supported objects of `𝒜_S`. -/
abbrev suppIn (S S' : Set X) : ObjectProperty (supp S : ObjectProperty (AsymCat G X)).FullSubcategory :=
  fun V => supp S' V.obj


end HSP
