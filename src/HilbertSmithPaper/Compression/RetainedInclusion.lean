import Mathlib
import HilbertSmithPaper.Compression.RetainedProjection

/-!
# Retained inclusion

For `i ≥ i₀`, `in_i : C_i → D_i` is the based inclusion of the span of the retained cells, the
transpose of the retained projection `pr_i`; for `i < i₀` it is zero (`C_i = 0`).

## Encoding

`retainedInc F i r` (the declaration of the article) is an abbreviation for the transpose of the
matrix `retainedProj F i r` of `pr_i` in degree `r`.
-/

namespace HSP.Compression

open HSP.ChainModels

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The based inclusion `in_i : (C_i)_r → (D_i)_r`, the transpose of `pr_i`. -/
noncomputable abbrev retainedInc (F : FixedLocalData p n D ρplus) (i : ℕ) (r : ℤ) :
    Matrix (Fin ((chainModel F.toLocalDatum i).X r).dim) (Fin ((compressed F r).as.n i)) ℚ :=
  (retainedProj F i r).transpose

end HSP.Compression
