import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Model.ChainModel
import HilbertSmithPaper.ChainModels.Grid.Model.ChainModelDualLabel
import HilbertSmithPaper.ChainModels.Approximations.TorusTestMap
import HilbertSmithPaper.Corner.RoundSphere

/-!
# Sphere labels of dual cells

The dual cell `a^*` of `(D_i^{N-*})_r`, `N = n + 4`, with torus label `x_a`, has the sphere label
`f_T(x_a) ∈ Sⁿ`, `f_T` the torus test map of radius `ρ`.

## Encoding

`dualSphereLabel A ρ i r a` (the declaration of the article) is `torusTestMap A ρ` applied to
`chainModelDualLabel A i r a`.
-/

open scoped NNReal

namespace HSP.ChainModels

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The sphere label `f_T(x_b)` of the dual cell `a^*` of `(D_i^{N-*})_r`. -/
noncomputable def dualSphereLabel (A : LocalDatum p n D ρplus) (ρ : ℝ) (i : ℕ) (r : ℤ)
    (a : Fin ((chainModel A i).X ((n + 4 : ℕ) - r)).dim) : Corner.RoundSphere n :=
  torusTestMap A ρ (chainModelDualLabel A i r a)

end HSP.ChainModels
