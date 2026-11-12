import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Model.ChainModel
import HilbertSmithPaper.ChainModels.Grid.Model.ChainModelLabel
import HilbertSmithPaper.ChainModels.Approximations.TorusTestMap
import HilbertSmithPaper.Categories.Asymptotic.Propagation
import HilbertSmithPaper.Corner.RoundSphere

/-!
# Sphere labels

A cell `b` of `D_i` with torus label `x_b` has the sphere label `s_b = f_T(x_b) ∈ Sⁿ`, `f_T` the
torus test map of radius `ρ`.

## Encoding

`Sⁿ` with `d_S` is `Corner.RoundSphere n`. `sphereLabel A ρ i r a` (the declaration of the
article) is the label of the basis cell `a` of `(D_i)_r`.
-/

open scoped NNReal

namespace HSP.ChainModels

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The *sphere label* `s_b = f_T(x_b)` of the basis cell `b = a` of `(D_i)_r`. -/
noncomputable def sphereLabel (A : LocalDatum p n D ρplus) (ρ : ℝ) (i : ℕ) (r : ℤ)
    (a : Fin ((chainModel A i).X r).dim) : Corner.RoundSphere n :=
  torusTestMap A ρ (chainModelLabel A i r a)

end HSP.ChainModels
