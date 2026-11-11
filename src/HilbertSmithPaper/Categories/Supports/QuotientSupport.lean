import HilbertSmithPaper.Categories.Supports.RelativeSupportAdditive
import HilbertSmithPaper.LTheory.Base.Categories.FiltrationQuotient

/-!
# Supported objects of a support quotient

For `S, Z, Y ⊆ X`, `𝒰_Y` (`HSP.quotSupp S Z Y`) is the predicate "`Y`-supported" on the objects of
`𝒜_S/𝒜_Z = FiltQuot (suppIn S Z)`.
-/

open CategoryTheory

namespace HSP

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

/-- `𝒰_Y ⊂ 𝒜_S/𝒜_Z`: the objects `⟨M⟩` with `M` `Y`-supported. -/
abbrev quotSupp (S Z Y : Set X) : ObjectProperty (FiltQuot (suppIn (G := G) S Z)) :=
  fun M => supp Y M.as.obj


end HSP
