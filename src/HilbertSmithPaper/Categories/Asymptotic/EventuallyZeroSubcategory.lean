import Mathlib
import HilbertSmithPaper.Categories.Asymptotic.PointSequenceCategory

/-!
# Finite-support subcategory

`𝒮_𝐆 ⊂ 𝒫_𝐆` is the full subcategory of the sequence category on the objects `(n_i)` whose
coordinate `n_i` is the zero object `0` for all but finitely many `i`.

Lean encoding: `HSP.SCat G : ObjectProperty (PCat G)`, the predicate
`{i | n_i ≠ 0}.Finite`; the full subcategory is `(SCat G).FullSubcategory`.
-/

open CategoryTheory

namespace HSP

variable {p : ℕ}

/-- The finite-support subcategory `𝒮_𝐆 ⊂ 𝒫_𝐆`: the objects `(n_i)` with `n_i = 0` for all but
finitely many `i`. -/
def SCat (G : GroupSeq p) : ObjectProperty (PCat G) :=
  fun X => {i | (X.coord i).n ≠ 0}.Finite

end HSP
