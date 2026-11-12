import Mathlib
import HilbertSmithPaper.LocalData.Control.FixedLocalData
import HilbertSmithPaper.ChainModels.Approximations.TorusTestMap
import HilbertSmithPaper.ChainModels.Grid.Torus

/-!
# The test preimage

For fixed local data with buffer radius `t` and torus test map `f_T` (of the pinch radius `ρ`),
`testPreimage F` is `K_t = f_T⁻¹(B̄(0, t)) ⊆ 𝕋ⁿ`, the preimage under `f_T` of the image of the
closed Euclidean ball `B̄(0, t) ⊆ ℝⁿ` in `Sⁿ`.
-/

namespace HSP.Compression

open HSP.ChainModels

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The set `K_t = f_T⁻¹(B̄(0, t)) ⊆ 𝕋ⁿ`, for the torus test map `f_T` of the pinch radius `ρ`
and the buffer radius `t`. -/
def testPreimage (F : FixedLocalData p n D ρplus) : Set (Torus n) :=
  torusTestMap F.toLocalDatum F.ρ ⁻¹'
    ((↑) '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) F.t)

end HSP.Compression
