import Mathlib
import HilbertSmithPaper.Compression.RetainedInclusion

/-!
# Projection onto the discarded cells

`Q_i = 1 - in_i pr_i : D_i → D_i`. For `i ≥ i₀` it is the based projection onto the span of the
discarded cells; for `i < i₀` it is the identity (`in_i = 0`, `pr_i = 0`). On cochains, `Q_i^*`
is its transpose.

## Encoding

`discardProj F i r` (the declaration of the article) is an abbreviation for
`1 - retainedInc F i r * retainedProj F i r`, the matrix of `Q_i` in degree `r`.
-/

namespace HSP.Compression

open HSP.ChainModels

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- `Q_i = 1 - in_i pr_i` on `(D_i)_r`. -/
noncomputable abbrev discardProj (F : FixedLocalData p n D ρplus) (i : ℕ) (r : ℤ) :
    Matrix (Fin ((chainModel F.toLocalDatum i).X r).dim)
      (Fin ((chainModel F.toLocalDatum i).X r).dim) ℚ :=
  1 - retainedInc F i r * retainedProj F i r

end HSP.Compression
