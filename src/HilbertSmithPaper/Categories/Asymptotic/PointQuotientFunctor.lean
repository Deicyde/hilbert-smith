import Mathlib
import HilbertSmithPaper.Categories.Asymptotic.PointQuotient

/-!
# The quotient functor of the point category

The quotient functor `q : 𝒫_𝐆 → 𝒱_𝐆 = 𝒫_𝐆 ⧸ 𝒮_𝐆`, a duality functor with `ξ = id`, so it is
strict.

## Encoding

`VCat.q G` (the declaration of the article) is the quotient functor `FiltQuot.q` of the
filtration quotient by the finite-support subcategory `SCat G`.
-/

namespace HSP.VCat

variable {p : ℕ} (G : GroupSeq p)

/-- The quotient functor `q : 𝒫_𝐆 → 𝒱_𝐆`, a duality functor with `ξ = id`. -/
def q : DualFunctor (PCat G) (VCat G) := FiltQuot.q (SCat G)

end HSP.VCat
