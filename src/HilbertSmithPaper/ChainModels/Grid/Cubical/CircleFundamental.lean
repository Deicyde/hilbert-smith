import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Cubical.CircleComplex

/-!
# Fundamental chain of the circle complex

The fundamental chain `∑_w e_w ∈ S_{k,1}`.

## Encoding

`circleFundamental k` (the declaration of the article) is the column of ones, a morphism from
`ℚ = ⟨1⟩`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.ChainModels

open FreeQ

/-- The fundamental chain of `S_k`, `∑_w e_w`, as a column. -/
def circleFundamental (k : ℕ) : (⟨1⟩ : FreeQ) ⟶ (circleComplex k).X 1 :=
  ofMatrix (Matrix.of fun _ _ => 1)

end HSP.ChainModels
