import Mathlib
import HilbertSmithPaper.LocalData.Chart.LocalDatum

/-!
# Completed cutoff

The cutoff `θ(x) = min(1, max(0, 3 - 2|x|))` on `ℝⁿ`: `1` on `B̄(0,1)`, `0` off `B(0,3/2)`.

## Encoding

`completedCutoff x` (the declaration of the article), with `ℝⁿ = EuclideanSpace ℝ (Fin n)`.
-/

namespace HSP.ChainModels

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The cutoff `θ(x) = min(1, max(0, 3 - 2|x|))`. -/
noncomputable def completedCutoff (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  min 1 (max 0 (3 - 2 * ‖x‖))

end HSP.ChainModels
