import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Cubical.CircleCell

/-!
# Labels of the circle cells

The cell `[w]` of `S_k` is labelled `4w/k` and the cell `e_w` is labelled `(4w+2)/k`, in `ℝ/4ℤ`: the
centers of the cells. A dual basis vector carries the label of its cell.

## Encoding

`circleLabel k r a` (the declaration of the article) is the label of the `a`-th basis vector of
`S_{k,r}`, read off its cell `circleCell k r a`.
-/

namespace HSP.ChainModels

open FreeQ

variable (k : ℕ)

/-- The label of a cell of `S_{k,r}` (and of its dual): its center, `4w/k` or `(4w+2)/k`. -/
noncomputable def circleLabel (r : ℤ) (a : Fin ((circleComplex k).X r).dim) :
    AddCircle (4 : ℝ) :=
  ((4 * ((circleCell k r a).1 : ℕ) + if (circleCell k r a).2 then 2 else 0) / k : ℝ)

end HSP.ChainModels
