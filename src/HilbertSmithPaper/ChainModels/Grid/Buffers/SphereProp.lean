import Mathlib
import HilbertSmithPaper.ChainModels.Approximations.TorusTestMap
import HilbertSmithPaper.Categories.Asymptotic.Propagation
import HilbertSmithPaper.Corner.RoundSphere

/-!
# Sphere propagation

The sphere propagation of a matrix `u` whose source and target cells carry torus labels `x` and
`x'`: its propagation for the sphere labels `f_T ∘ x`, `f_T ∘ x'` and the round metric `d_S`.

## Encoding

`sphereProp A ρ x x' u` (the declaration of the article), for the torus test map `f_T` of
radius `ρ`.
-/

open scoped NNReal

namespace HSP.ChainModels

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The *sphere propagation* of a matrix `u` whose source and target cells carry the torus labels
`x` and `x'`: its propagation for the sphere labels `f_T ∘ x`, `f_T ∘ x'` and `d_S`. -/
noncomputable def sphereProp (A : LocalDatum p n D ρplus) (ρ : ℝ) {B B' : Type*} [Fintype B]
    [Fintype B'] (x : B → Torus n) (x' : B' → Torus n) (u : Matrix B' B ℚ) : ℝ≥0 :=
  prop (fun b => (torusTestMap A ρ (x b) : Corner.RoundSphere n))
    (fun b' => (torusTestMap A ρ (x' b') : Corner.RoundSphere n)) u

end HSP.ChainModels
