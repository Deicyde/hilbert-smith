import Mathlib
import HilbertSmithPaper.ChainModels.Grid.BufferedCells
import HilbertSmithPaper.ChainModels.Grid.ControlLabels

/-!
# Buffered restriction of a matrix

For `v ≤ v'` and a matrix `u` between based modules spanned by cells of `D_i` or of
`D_i^{N-*}`, the restriction `u^{[v,v']} = p_{v'} u ι_v` keeps the rows of the buffered cells
`𝓑_i(v')` of the target and the columns of the buffered cells `𝓑_i(v)` of the source;
`u^{[v]} = u^{[v,v]}`. The spans of buffered cells carry the control labels.

## Encoding

`restrict S' S u` (the declaration of the article) is `u.submatrix` along the inclusions of the
subsets `S ⊆ B` (source cells, e.g. `bufferedCells A ρ i r v`) and `S' ⊆ B'` (target cells, e.g.
`bufferedCells A ρ i r' v'`): composing with the based inclusion `ι` and projection `p` of the
spans selects exactly these rows and columns.
-/

namespace HSP.ChainModels

/-- The *restriction* `p_{S'} u ι_S` of a matrix `u : ℚ^B → ℚ^{B'}` to the spans of the cells
`S ⊆ B` and `S' ⊆ B'`: for the buffered cells `𝓑_i(v)` and `𝓑_i(v')` this is `u^{[v,v']}`. -/
def restrict {B B' : Type*} (S' : Set B') (S : Set B) (u : Matrix B' B ℚ) : Matrix S' S ℚ :=
  u.submatrix Subtype.val Subtype.val

end HSP.ChainModels
