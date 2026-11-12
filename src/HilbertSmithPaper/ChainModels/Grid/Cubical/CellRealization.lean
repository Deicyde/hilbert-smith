import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Cubical.CircleComplex

/-!
# Realization of a circle cell

The realization of the cell `[w]` of `S_k` is the point `4w/k` of `ℝ/4ℤ`, and that of `e_w` is the
image of `[4w/k, 4(w+1)/k]`.

## Encoding

`ℝ/4ℤ` is `AddCircle 4` and a cell is a pair `(w, b) : Fin k × Bool`, `b = true` for `e_w`.
`cellRealization k b` is the declaration of the article.
-/

namespace HSP.ChainModels

/-- The realization of a cell of `S_k`: the point `4w/k`, or the arc from `4w/k` to
`4(w+1)/k`. -/
def cellRealization (k : ℕ) (b : Fin k × Bool) : Set (AddCircle (4 : ℝ)) :=
  if b.2 then (fun t : ℝ => (t : AddCircle (4 : ℝ))) ''
      Set.Icc (4 * (b.1 : ℕ) / k : ℝ) (4 * ((b.1 : ℕ) + 1) / k)
  else {((4 * (b.1 : ℕ) / k : ℝ) : AddCircle (4 : ℝ))}

end HSP.ChainModels
