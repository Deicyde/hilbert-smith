import Mathlib

/-!
# The torus

`𝕋ⁿ = (ℝ/4ℤ)ⁿ`, with the metric `d_∞`, the maximum of the circle distances.

## Encoding

* `𝕋ⁿ` is `Fin n → AddCircle (4 : ℝ)`. Mathlib's metric on it is the maximum of the circle
  distances, so `d_∞` is `dist`, and its norm `‖x‖` is `d_∞(x, 0)`.
* `N_r(X)` is `Metric.cthickening r X`, the points at `d_∞`-distance at most `r` from `X`.
* The instance `Fact (0 < 4)`, which Mathlib's `AddCircle` API needs, lives here.
-/

namespace HSP.ChainModels

/-- `4 > 0`, for the circle `ℝ/4ℤ`. -/
instance fact_zero_lt_four : Fact ((0 : ℝ) < 4) := ⟨by norm_num⟩

/-- The torus `𝕋ⁿ = (ℝ/4ℤ)ⁿ`; its `dist` is `d_∞`, the maximum of the circle distances. -/
abbrev Torus (n : ℕ) : Type := Fin n → AddCircle (4 : ℝ)

end HSP.ChainModels
