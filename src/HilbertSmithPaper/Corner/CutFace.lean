import Mathlib
import HilbertSmithPaper.Corner.RoundSphere

/-!
# The cube face

For `n`, `s` and `m`, the cube face `B_m = [-s, s]^{n-m+1} × {s}^{m-1} ⊆ ℝ^n ⊆ S^n`
(`HSP.Corner.cutB`). Coordinates are indexed by `k : Fin n`, so the article's
`k ≤ n - m + 1` (counting from `1`) is `k.val < n - m + 1` (counting from `0`).

Lean encoding. The definition takes only `n` and `s` (and `m`); the conditions `n ≥ 1`,
`s > 0` and `1 ≤ m ≤ n` are hypotheses of the lemmas about the cut sets (the cut flag).
-/

namespace HSP.Corner

/-- The cube face `B_m = [-s, s]^{n-m+1} × {s}^{m-1} ⊆ ℝ^n ⊆ S^n`: the first `n - m + 1`
coordinates lie in `[-s, s]` and the remaining `m - 1` equal `s`. -/
def cutB (n : ℕ) (s : ℝ) (m : ℕ) : Set (RoundSphere n) :=
  ((↑) : EuclideanSpace ℝ (Fin n) → RoundSphere n) ''
    {x | ∀ k : Fin n, (k.val < n - m + 1 → |x k| ≤ s) ∧ (n - m + 1 ≤ k.val → x k = s)}

end HSP.Corner
