import Mathlib
import HilbertSmithPaper.LocalData.Chart.LocalDatum

/-!
# Fixed local data

Fixed local data with constants `(D, ρplus)` in dimension `n`: a local datum with these constants,
a pinch radius `0 < ρ < ρplus`, and buffer radii `0 < r < R < t < u` (Euclidean radii about `0`).
The test map of radius `ρ` and the control space are read off from the underlying local datum;
the exterior and the cut sets are defined by the corner chapter from the control space and `R`.
-/

namespace HSP

/-- *Fixed local data*: a local datum with constants `(D, ρplus)`, a pinch radius
`0 < ρ < ρplus` and buffer radii `0 < r < R < t < u`. -/
structure FixedLocalData (p : ℕ) [Fact p.Prime] (n : ℕ) (D ρplus : ℝ) extends
    LocalDatum p n D ρplus where
  /-- The pinch radius. -/
  ρ : ℝ
  /-- The pinch radius is positive. -/
  ρ_pos : 0 < ρ
  /-- The pinch radius is less than `ρplus`. -/
  ρ_lt : ρ < ρplus
  /-- The innermost buffer radius. -/
  r : ℝ
  /-- The second buffer radius (the radius of the exterior). -/
  R : ℝ
  /-- The third buffer radius. -/
  t : ℝ
  /-- The outer buffer radius. -/
  u : ℝ
  /-- `0 < r`. -/
  r_pos : 0 < r
  /-- `r < R`. -/
  r_lt_R : r < R
  /-- `R < t`. -/
  R_lt_t : R < t
  /-- `t < u`. -/
  t_lt_u : t < u

end HSP
