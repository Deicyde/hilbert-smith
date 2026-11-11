import Mathlib
import HilbertSmithPaper.Corner.CutFace

/-!
# The boundary of the cube face

`Y_0 = S^n` and, for `m ≥ 1`, `Y_m = {x ∈ B_m : |x_k| = s for some k ≤ n - m + 1}`, the boundary
of the cube face `B_m` in its affine plane (`HSP.Corner.cutY`).

Lean encoding. The definition takes only `n` and `s` (and `m`); the conditions `n ≥ 1`,
`s > 0` and `1 ≤ m ≤ n` are hypotheses of the lemmas about the cut sets (the cut flag).
-/

namespace HSP.Corner

/-- `Y_0 = S^n`, and for `m ≥ 1`, `Y_m = {x ∈ B_m : |x_k| = s for some k ≤ n - m + 1}`, the
boundary of `B_m` in the affine plane `ℝ^{n-m+1} × {s}^{m-1}`. -/
def cutY (n : ℕ) (s : ℝ) : ℕ → Set (RoundSphere n)
  | 0 => Set.univ
  | m + 1 => cutB n s (m + 1) ∩
      ((↑) : EuclideanSpace ℝ (Fin n) → RoundSphere n) ''
        {x | ∃ k : Fin n, k.val < n - (m + 1) + 1 ∧ |x k| = s}

end HSP.Corner
