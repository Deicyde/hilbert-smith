import Mathlib
import HilbertSmithPaper.Compression.StartIndex

/-!
# Bound sequence

With the null sequence `(ε'_i)` chosen in "buffers hold eventually" and the start index `i₀`, the
bound sequence is `δ_i = ε'_i` for `i ≥ i₀` and `δ_i = 0` for `i < i₀`.

## Encoding

`bound F` (the declaration of the article) is `δ`; the chosen `(ε'_i)` is
`(buffer_eventually F).choose`.
-/

namespace HSP.Compression

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

open Classical in
/-- The *bound sequence* `δ_i = ε'_i` for `i ≥ i₀` and `δ_i = 0` for `i < i₀`. -/
noncomputable def bound (F : FixedLocalData p n D ρplus) (i : ℕ) : ℝ :=
  if startIndex F ≤ i then (buffer_eventually F).choose i else 0

end HSP.Compression
