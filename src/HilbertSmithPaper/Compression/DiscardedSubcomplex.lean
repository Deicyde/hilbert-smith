import Mathlib
import HilbertSmithPaper.Compression.RetainedProjection

/-!
# The discarded cells form a subcomplex

With `pr_i` the based projection of `D_i` onto the span of the retained cells and `Q_i` the based
projection onto the span of the discarded cells, `pr_i d Q_i = 0` and `Q_i^* d^* pr_i^* = 0`.

## Encoding

* `Q_i = 1 - in_i pr_i` is `discardProj`; the duals `Q_i^*`, `d^*`, `pr_i^*` are transposes, so
  the second identity is `Q_iᵀ dᵀ pr_iᵀ = 0`.
* `pr_d_Q` (the declaration of the article) states both identities for the component
  `(chainModel _ i).d r s` of the differential, for all `r s` (it is `0` unless `s = r - 1`), so
  that callers can use any spelling of the target degree; and for every `i` (for `i < i₀`,
  `pr_i` has no rows).
-/

namespace HSP.Compression

open HSP.ChainModels FreeQ
open scoped Matrix

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- **The discarded cells form a subcomplex.** `pr_i d Q_i = 0` and `Q_i^* d^* pr_i^* = 0`, for
the component `d : (D_i)_r → (D_i)_s` of the differential of `D_i`. -/
theorem pr_d_Q (F : FixedLocalData p n D ρplus) (i : ℕ) (r s : ℤ) :
    retainedProj F i s * toMatrix ((chainModel F.toLocalDatum i).d r s) *
        discardProj F i r = 0 ∧
      (discardProj F i r)ᵀ * (toMatrix ((chainModel F.toLocalDatum i).d r s))ᵀ *
        (retainedProj F i s)ᵀ = 0 := by
  sorry

end HSP.Compression
