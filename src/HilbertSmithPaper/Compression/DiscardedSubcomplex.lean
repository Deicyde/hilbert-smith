import Mathlib
import HilbertSmithPaper.Compression.CompressedComplex

/-!
# The discarded cells form a subcomplex

With `pr_i` the based projection of `D_i` onto the span of the retained cells and `Q_i` the based
projection onto the span of the discarded cells, `pr_i d Q_i = 0` and `Q_i^* d^* pr_i^* = 0`.

## Encoding

* `Q_i = 1 - in_i pr_i` is `discardProj`; `d` out of degree `r` is the matrix of
  `(chainModel _ i).d r (r - 1)`; the duals `Q_i^*`, `d^*`, `pr_i^*` are transposes, so the
  second identity is `Q_iᵀ dᵀ pr_iᵀ = 0`.
* `pr_d_Q` (the declaration of the article) states both identities in each degree `r`, for every
  `i` (for `i < i₀`, `pr_i` has no rows).
-/

namespace HSP.Compression

open HSP.ChainModels FreeQ
open scoped Matrix

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- **The discarded cells form a subcomplex.** `pr_i d Q_i = 0` and `Q_i^* d^* pr_i^* = 0`, for
the differential `d` of `D_i` out of degree `r`. -/
theorem pr_d_Q (F : FixedLocalData p n D ρplus) (i : ℕ) (r : ℤ) :
    retainedProj F i (r - 1) * toMatrix ((chainModel F.toLocalDatum i).d r (r - 1)) *
        discardProj F i r = 0 ∧
      (discardProj F i r)ᵀ * (toMatrix ((chainModel F.toLocalDatum i).d r (r - 1)))ᵀ *
        (retainedProj F i (r - 1))ᵀ = 0 := by
  sorry

end HSP.Compression
