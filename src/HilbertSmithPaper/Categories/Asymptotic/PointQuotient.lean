import Mathlib
import HilbertSmithPaper.Categories.Asymptotic.PointFiltration
import HilbertSmithPaper.Categories.Asymptotic.PointIdeal
import HilbertSmithPaper.LTheory.Base.Categories.FiltrationQuotient

/-!
# Point category

`𝒱_𝐆 = 𝒫_𝐆 ⧸ 𝒮_𝐆` is the quotient of the sequence category by the finite-support subcategory
(`HSP.VCat G`, the paper's quotient `HSP.FiltQuot` by `HSP.SCat G`); the quotient functor
`q : 𝒫_𝐆 → 𝒱_𝐆` is `HSP.VCat.q`, in its own module. The subcategory carries the point
filtration `HSP.SCat.karoubiFiltration`. By the point ideal, the morphisms of `𝒱_𝐆` are the
sequences `(u_i)` modulo equality for all but finitely many `i` (a remark of the article, not
stated here).
-/

open CategoryTheory

namespace HSP

variable {p : ℕ}

/-- The point category `𝒱_𝐆 = 𝒫_𝐆 ⧸ 𝒮_𝐆`. -/
abbrev VCat (G : GroupSeq p) : Type := FiltQuot (SCat G)

end HSP
