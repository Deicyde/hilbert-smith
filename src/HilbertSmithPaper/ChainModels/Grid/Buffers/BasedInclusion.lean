import Mathlib

/-!
# Based inclusion

For a set of cells `B` and a subset `S ⊆ B`, the based inclusion `ι_S : ℚ^S → ℚ^B` sends the basis
vector of `s ∈ S` to that of `s ∈ B`. For the buffered cells `𝓑(v)` it is `ι_v`.

## Encoding

`basedInc S` (the declaration of the article) is the matrix in `ℚ^{B × S}` with entry `1` at
`(b, s)` when `b = s` and `0` otherwise (classical decidability of equality).
-/

namespace HSP.ChainModels

open Classical in
/-- The *based inclusion* `ι_S : ℚ^S → ℚ^B` of a subset `S ⊆ B`, as a matrix. -/
noncomputable def basedInc {B : Type*} (S : Set B) : Matrix B S ℚ :=
  Matrix.of fun b s => if b = s.1 then 1 else 0

end HSP.ChainModels
