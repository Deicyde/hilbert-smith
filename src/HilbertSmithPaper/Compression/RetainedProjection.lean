import Mathlib
import HilbertSmithPaper.Compression.CompressedComplex

/-!
# Retained projection

For `i ≥ i₀`, `pr_i : D_i → C_i` is the based projection onto the span of the retained cells and
`in_i : C_i → D_i` the based inclusion, and `Q_i = 1 - in_i pr_i`; for `i < i₀` they are zero
(`C_i = 0`) and `Q_i = 1`. On cochains, `in_i^*`, `pr_i^*` and `Q_i^*` are their transposes.

## Encoding

`retainedProj F i r` (the declaration of the article) is the matrix of `pr_i` in degree `r`, with
rows the basis of `(C_i)_r` (the retained cells in increasing order, `compressedCell`); the
abbreviations `retainedInc F i r` (`in_i`, its transpose) and `discardProj F i r` (`Q_i`) belong to
the same article.
-/

namespace HSP.Compression

open HSP.ChainModels

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

open Classical in
/-- The based projection `pr_i : (D_i)_r → (C_i)_r`. -/
noncomputable def retainedProj (F : FixedLocalData p n D ρplus) (i : ℕ) (r : ℤ) :
    Matrix (Fin ((compressed F r).as.n i)) (Fin ((chainModel F.toLocalDatum i).X r).dim) ℚ :=
  Matrix.of fun b a => if hi : startIndex F ≤ i then (if a = compressedCell F hi r b then 1 else 0)
    else 0

/-- The based inclusion `in_i : (C_i)_r → (D_i)_r`. -/
noncomputable abbrev retainedInc (F : FixedLocalData p n D ρplus) (i : ℕ) (r : ℤ) :
    Matrix (Fin ((chainModel F.toLocalDatum i).X r).dim) (Fin ((compressed F r).as.n i)) ℚ :=
  (retainedProj F i r).transpose

/-- `Q_i = 1 - in_i pr_i` on `(D_i)_r`. -/
noncomputable abbrev discardProj (F : FixedLocalData p n D ρplus) (i : ℕ) (r : ℤ) :
    Matrix (Fin ((chainModel F.toLocalDatum i).X r).dim)
      (Fin ((chainModel F.toLocalDatum i).X r).dim) ℚ :=
  1 - retainedInc F i r * retainedProj F i r

end HSP.Compression
