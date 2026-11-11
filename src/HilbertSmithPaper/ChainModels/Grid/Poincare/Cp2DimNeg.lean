import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Cp2Cells

/-!
# The cells of CP² vanish in negative degrees
-/

open CategoryTheory

namespace HSP.ChainModels

open FreeQ DualCat

/-- The cells of `CP²` vanish in negative degrees. -/
lemma cp2Complex_X_dim_neg : ∀ q < 0, (cp2Complex.X q).dim = 0 := by
  intro q hq
  rcases q with q | q
  · exact absurd hq (by simp)
  · rfl

end HSP.ChainModels
