import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Cubical.CircleComplex

/-!
# Augmentation of the circle complex

The augmentation `ε : S_{k,0} → ℚ`, `ε[w] = 1`.

## Encoding

`circleAug k` (the declaration of the article) is the row of ones.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.ChainModels

open FreeQ

/-- The augmentation `ε[w] = 1` of `S_k`, a row of ones. -/
def circleAug (k : ℕ) : (circleComplex k).X 0 ⟶ (⟨1⟩ : FreeQ) :=
  ofMatrix (Matrix.of fun _ _ => 1)

end HSP.ChainModels
