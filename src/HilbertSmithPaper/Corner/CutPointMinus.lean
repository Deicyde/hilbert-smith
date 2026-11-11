import Mathlib
import HilbertSmithPaper.Corner.RoundSphere

/-!
# The point y₋

The point `y_- = (-s, s, …, s)` of `ℝ^n ⊆ S^n` (`HSP.Corner.yMinus`).
-/

namespace HSP.Corner

/-- The point `y_- = (-s, s, …, s)`. -/
noncomputable def yMinus (n : ℕ) (s : ℝ) : RoundSphere n :=
  ((WithLp.toLp 2 fun k : Fin n => if k.val = 0 then -s else s : EuclideanSpace ℝ (Fin n)) :
    RoundSphere n)

end HSP.Corner
