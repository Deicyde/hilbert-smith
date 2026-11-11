import Mathlib
import HilbertSmithPaper.Corner.RoundSphere

/-!
# The point y₊

The point `y_+ = (s, s, …, s)` of `ℝ^n ⊆ S^n` (`HSP.Corner.yPlus`).
-/

namespace HSP.Corner

/-- The point `y_+ = (s, s, …, s)`. -/
noncomputable def yPlus (n : ℕ) (s : ℝ) : RoundSphere n :=
  ((WithLp.toLp 2 fun _ : Fin n => s : EuclideanSpace ℝ (Fin n)) : RoundSphere n)

end HSP.Corner
