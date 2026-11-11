import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Cubical.CircleComplex

/-!
# The cell of a basis vector of `S_k`

The `w`-th basis vector of `S_{k,0}` is the cell `[w]`, and that of `S_{k,1}` is `e_w`.

## Encoding

A cell is a pair `(w, b) : Fin k × Bool`, `b = true` for `e_w`. `circleCell k r w` (the
declaration of the article) is the cell of the `w`-th basis vector of `S_{k,r}`.
-/

namespace HSP.ChainModels

/-- The cell `[w]` (for `r = 0`) or `e_w` (for `r = 1`) of the `w`-th basis vector of `S_{k,r}`. -/
def circleCell (k : ℕ) : ∀ r : ℤ, Fin ((circleComplex k).X r).dim → Fin k × Bool
  | .ofNat 0, w => (w, false)
  | .ofNat 1, w => (w, true)
  | .ofNat (_ + 2), w => w.elim0
  | .negSucc _, w => w.elim0

end HSP.ChainModels
