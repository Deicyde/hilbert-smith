import HilbertSmithPaper.Categories.Supports.SupportSubcategory
import HilbertSmithPaper.LTheory.Base.Categories.FiltrationQuotient

/-!
# Exterior quotient

For `Z ⊆ X`, the exterior quotient `ℬ_{𝐆,Z}(X) = 𝒜_𝐆(X)/𝒜_Z` (`HSP.Ext G X Z`) is the quotient of
the asymptotic category by its support subcategory `𝒜_Z`, a full additive subcategory closed under
duality (`HSP.isDualAdditive_supp`). It is an `abbrev` for `FiltQuot (supp Z)`, so it carries the
duality category structure of the quotient, and the quotient functor `q = FiltQuot.q (supp Z)` is
a strict duality functor. Closedness and invariance of `Z` are not needed for the definition.
-/

namespace HSP

variable {p : ℕ}

/-- The *exterior quotient* `ℬ_{𝐆,Z}(X) = 𝒜_𝐆(X)/𝒜_Z`. -/
abbrev Ext (G : GroupSeq p) (X : Type*) [MetricSpace X] [AddAction (ZMod p) X] (Z : Set X) :=
  FiltQuot (supp Z : CategoryTheory.ObjectProperty (AsymCat G X))

end HSP
