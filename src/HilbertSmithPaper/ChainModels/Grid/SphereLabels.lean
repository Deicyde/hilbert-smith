import Mathlib
import HilbertSmithPaper.ChainModels.Grid.ChainModel
import HilbertSmithPaper.ChainModels.Approximations.TorusTestMap
import HilbertSmithPaper.Categories.Asymptotic.Propagation
import HilbertSmithPaper.Corner.StandingData

/-!
# Sphere labels

A cell `b` of `D_i`, or its dual, with torus label `x_b`, has the sphere label
`s_b = f_T(x_b) ∈ Sⁿ`, `f_T` the torus test map of radius `ρ`. The sphere propagation of a matrix
between spans of such cells is its propagation for the sphere labels and the round metric `d_S`.

## Encoding

`Sⁿ` with `d_S` is `Corner.RoundSphere n`. `sphereLabel A ρ i r a` (the declaration of the
article) is the label of the basis cell `a` of `(D_i)_r`, `dualSphereLabel` that of the dual cell
`a^*` of `(D_i^{N-*})_r`; `sphereProp` is the propagation of a matrix whose source and target
cells have torus labels `x`, `x'` (cells of `D_i` or duals), for the labels `f_T ∘ x`, `f_T ∘ x'`.
-/

open scoped NNReal

namespace HSP.ChainModels

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The *sphere label* `s_b = f_T(x_b)` of the basis cell `b = a` of `(D_i)_r`. -/
noncomputable def sphereLabel (A : LocalDatum p n D ρplus) (ρ : ℝ) (i : ℕ) (r : ℤ)
    (a : Fin ((chainModel A i).X r).dim) : Corner.RoundSphere n :=
  torusTestMap A ρ (chainModelLabel A i r a)

/-- The sphere label `f_T(x_b)` of the dual cell `a^*` of `(D_i^{N-*})_r`. -/
noncomputable def dualSphereLabel (A : LocalDatum p n D ρplus) (ρ : ℝ) (i : ℕ) (r : ℤ)
    (a : Fin ((chainModel A i).X ((n + 4 : ℕ) - r)).dim) : Corner.RoundSphere n :=
  torusTestMap A ρ (chainModelDualLabel A i r a)

/-- The *sphere propagation* of a matrix `u` whose source and target cells carry the torus labels
`x` and `x'`: its propagation for the sphere labels `f_T ∘ x`, `f_T ∘ x'` and `d_S`. -/
noncomputable def sphereProp (A : LocalDatum p n D ρplus) (ρ : ℝ) {B B' : Type*} [Fintype B]
    [Fintype B'] (x : B → Torus n) (x' : B' → Torus n) (u : Matrix B' B ℚ) : ℝ≥0 :=
  prop (fun b => (torusTestMap A ρ (x b) : Corner.RoundSphere n))
    (fun b' => (torusTestMap A ρ (x' b') : Corner.RoundSphere n)) u

end HSP.ChainModels
