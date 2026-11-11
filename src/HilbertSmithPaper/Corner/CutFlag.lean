import Mathlib
import HilbertSmithPaper.Corner.CutSets

/-!
# The cut flag

For `n ≥ 1`, `s > 0` and every `1 ≤ m ≤ n`: `A_m` and `B_m` are closed in `S^n`,
`A_m ∪ B_m = Y_{m-1}` and `A_m ∩ B_m = Y_m`; moreover `Y_n = {y_-, y_+}` and `y_- ≠ y_+`.
-/

namespace HSP.Corner

/-- The cut flag: for `1 ≤ m ≤ n`, `A_m` and `B_m` are closed, `A_m ∪ B_m = Y_{m-1}` and
`A_m ∩ B_m = Y_m`; moreover `Y_n = {y_-, y_+}` and `y_- ≠ y_+`. -/
theorem cut_flag (n : ℕ) (hn : 1 ≤ n) (s : ℝ) (hs : 0 < s) :
    (∀ m : ℕ, 1 ≤ m → m ≤ n →
      IsClosed (cutA n s m) ∧ IsClosed (cutB n s m) ∧
        cutA n s m ∪ cutB n s m = cutY n s (m - 1) ∧
        cutA n s m ∩ cutB n s m = cutY n s m) ∧
      cutY n s n = {yMinus n s, yPlus n s} ∧ yMinus n s ≠ yPlus n s := by
  sorry

end HSP.Corner
