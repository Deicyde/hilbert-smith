import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Torus

/-!
# The torus has diameter at most 2

`d_∞(x, y) ≤ 2` for `x, y ∈ 𝕋ⁿ`.
-/

namespace HSP.ChainModels.Torus

variable {n : ℕ}

/-- `d_∞ ≤ 2` on the torus. -/
lemma dist_le_two (x y : Torus n) : dist x y ≤ 2 := by
  refine (dist_pi_le_iff zero_le_two).2 fun j => ?_
  rw [dist_eq_norm]
  have := AddCircle.norm_le_half_period (x := x j - y j) (p := (4 : ℝ)) (by norm_num)
  norm_num at this ⊢
  exact this

end HSP.ChainModels.Torus
