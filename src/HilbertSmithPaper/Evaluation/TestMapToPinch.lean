import Mathlib
import HilbertSmithPaper.LocalData.Control.FixedLocalData
import HilbertSmithPaper.Evaluation.CubicalPinch
import HilbertSmithPaper.ChainModels.Approximations.TorusTestMap
import HilbertSmithPaper.ChainModels.Grid.Torus

/-!
# The torus test map is homotopic to the cubical pinch

For fixed local data and every `s > 0` there is a continuous `H : [0,1] × 𝕋ⁿ → Sⁿ` with
`H(0, ·) = f_T` (the torus test map of the pinch radius `ρ`) and `H(1, ·) = κ` (the cubical pinch
for `s`). The time parameter is `unitInterval`.
-/

open OnePoint

namespace HSP.Evaluation

open HSP.ChainModels

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- *The torus test map is homotopic to the cubical pinch*: for fixed local data and `s > 0`
there is a continuous `H : [0,1] × 𝕋ⁿ → Sⁿ` with `H(0,x) = f_T(x)` and `H(1,x) = κ(x)`. -/
theorem torusTestMap_homotopic_pinch (F : FixedLocalData p n D ρplus) {s : ℝ} (hs : 0 < s) :
    ∃ H : unitInterval × Torus n → OnePoint (EuclideanSpace ℝ (Fin n)), Continuous H ∧
      (∀ x, H (0, x) = torusTestMap F.toLocalDatum F.ρ x) ∧
      ∀ x, H (1, x) = cubicalPinch n s hs x := by
  sorry

end HSP.Evaluation
