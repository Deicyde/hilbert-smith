import HilbertSmithPaper.Categories.Asymptotic.AsymptoticDuality

/-!
# Support subcategory

For `S ⊆ X`, `𝒜_S` (`HSP.supp S`) is the full subcategory of `𝒜_𝐆(X)` on the objects
`⟨(n_i, x_i)⟩` such that for every `ε > 0`, eventually all `x_i(k)` lie in the open
`ε`-thickening `Metric.thickening ε S` (empty when `S = ∅`, unlike a formulation through
`Metric.infDist`). The paper uses it for closed invariant `S`; the definition needs neither.

That `𝒜_S` is a full additive subcategory closed under duality is the instance
`HSP.isDualAdditive_supp` (support-dual-additive).
-/

open CategoryTheory CategoryTheory.Limits Filter

namespace HSP

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

/-- The *support subcategory* `𝒜_S`: the objects `(n_i, x_i)` of `𝒜_𝐆(X)` such that for every
`ε > 0`, eventually all `x_i(k)` lie in the open `ε`-thickening of `S`. -/
def supp (S : Set X) : ObjectProperty (AsymCat G X) :=
  fun P => ∀ ε > 0, ∀ᶠ i in atTop, ∀ k, P.as.x i k ∈ Metric.thickening ε S

end HSP
