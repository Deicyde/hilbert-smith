import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.BasedVectorSpaces

/-!
# The unit complex

The unit complex `𝟙`: `ℚ` in degree `0` and zero elsewhere, with zero differential.

## Encoding

`unitComplex` (the declaration of the article) is `ChainComplex.of` of the dimensions `unitDim`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.ChainModels

open FreeQ

/-- The number of cells of the unit complex `𝟙` in degree `r`: `1` in degree `0`, else `0`. -/
def unitDim : ℤ → ℕ
  | .ofNat 0 => 1
  | _ => 0

/-- The unit complex `𝟙`: `ℚ` in degree `0`. -/
def unitComplex : ChainComplex FreeQ ℤ :=
  ChainComplex.of (fun r => ⟨unitDim r⟩) (fun _ => 0) fun _ => zero_comp

end HSP.ChainModels
