import Mathlib
import HilbertSmithPaper.Compression.CompressedComplex

/-!
# Retained projection

For `i ≥ i₀`, `pr_i : D_i → C_i` is the based projection onto the span of the retained cells; for
`i < i₀` it is zero (`C_i = 0`). On cochains, `pr_i^*` is its transpose.

## Encoding

`retainedProj F i r` (the declaration of the article) is the matrix of `pr_i` in degree `r`, with
rows the basis of `(C_i)_r` (the retained cells in increasing order, `compressedCell`). The based
inclusion `in_i` and `Q_i = 1 - in_i pr_i` are `retainedInc` and `discardProj`, in their own
modules.
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

end HSP.Compression
