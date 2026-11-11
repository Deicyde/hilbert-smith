import Mathlib
import HilbertSmithPaper.Corner.RoundSphere

/-!
# The cut sets

For `n ≥ 1` and `s > 0`, in the round sphere `S^n = ℝ^n ∪ {∞}`, for `1 ≤ m ≤ n`:
* `B_m = [-s, s]^{n-m+1} × {s}^{m-1} ⊆ ℝ^n` (`HSP.Corner.cutB`);
* `Y_m = {x ∈ B_m : |x_k| = s for some k ≤ n - m + 1}`, the boundary of `B_m` in its affine plane
  (`HSP.Corner.cutY`, with `Y_0 = S^n`);
* `A_m = closure (Y_{m-1} \ B_m)` in `S^n` (`HSP.Corner.cutA`);
* `y_± = (±s, s, …, s)` (`HSP.Corner.yPlus`, `HSP.Corner.yMinus`).

Lean encoding. The sets take only `n`, `s` and `m : ℕ`; the conditions `n ≥ 1`, `s > 0` and
`1 ≤ m ≤ n` are hypotheses of the lemmas about them (the cut flag), not of the definitions.
Coordinates are indexed by `k : Fin n`, so the article's `k ≤ n - m + 1` (counting from `1`) is
`k.val < n - m + 1` (counting from `0`).
-/

namespace HSP.Corner

/-- The cube face `B_m = [-s, s]^{n-m+1} × {s}^{m-1} ⊆ ℝ^n ⊆ S^n`: the first `n - m + 1`
coordinates lie in `[-s, s]` and the remaining `m - 1` equal `s`. -/
def cutB (n : ℕ) (s : ℝ) (m : ℕ) : Set (RoundSphere n) :=
  ((↑) : EuclideanSpace ℝ (Fin n) → RoundSphere n) ''
    {x | ∀ k : Fin n, (k.val < n - m + 1 → |x k| ≤ s) ∧ (n - m + 1 ≤ k.val → x k = s)}

/-- `Y_0 = S^n`, and for `m ≥ 1`, `Y_m = {x ∈ B_m : |x_k| = s for some k ≤ n - m + 1}`, the
boundary of `B_m` in the affine plane `ℝ^{n-m+1} × {s}^{m-1}`. -/
def cutY (n : ℕ) (s : ℝ) : ℕ → Set (RoundSphere n)
  | 0 => Set.univ
  | m + 1 => cutB n s (m + 1) ∩
      ((↑) : EuclideanSpace ℝ (Fin n) → RoundSphere n) ''
        {x | ∃ k : Fin n, k.val < n - (m + 1) + 1 ∧ |x k| = s}

/-- `A_m = closure (Y_{m-1} \ B_m)`, the closure taken in `S^n`. -/
def cutA (n : ℕ) (s : ℝ) (m : ℕ) : Set (RoundSphere n) :=
  closure (cutY n s (m - 1) \ cutB n s m)

/-- The point `y_+ = (s, s, …, s)`. -/
noncomputable def yPlus (n : ℕ) (s : ℝ) : RoundSphere n :=
  ((WithLp.toLp 2 fun _ : Fin n => s : EuclideanSpace ℝ (Fin n)) : RoundSphere n)

/-- The point `y_- = (-s, s, …, s)`. -/
noncomputable def yMinus (n : ℕ) (s : ℝ) : RoundSphere n :=
  ((WithLp.toLp 2 fun k : Fin n => if k.val = 0 then -s else s : EuclideanSpace ℝ (Fin n)) :
    RoundSphere n)

end HSP.Corner
