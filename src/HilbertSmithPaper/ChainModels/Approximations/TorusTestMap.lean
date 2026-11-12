import Mathlib
import HilbertSmithPaper.ChainModels.Torus.Lift
import HilbertSmithPaper.LocalData.Chart.TestMap
import HilbertSmithPaper.ChainModels.Grid.Torus

/-!
# Torus test map

`f_T : 𝕋ⁿ → Sⁿ`, `f_T(x) = f(x̃)`, with `x̃ ∈ [-2,2)ⁿ` the lift of `x` and `f` the test map of
radius `ρ`. Balls of `ℝⁿ` of radius `< 2` also denote their images `q '' B` in the torus; this is
notation, not a declaration.
-/

namespace HSP.ChainModels

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The *torus test map* `f_T(x) = f(x̃)`, `f` the test map of radius `ρ` of the local datum. -/
noncomputable def torusTestMap (A : LocalDatum p n D ρplus) (ρ : ℝ) (x : Torus n) :
    OnePoint (EuclideanSpace ℝ (Fin n)) :=
  A.testMap ρ (Torus.lift x)

end HSP.ChainModels
