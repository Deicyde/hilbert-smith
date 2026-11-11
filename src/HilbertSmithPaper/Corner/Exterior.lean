import Mathlib
import HilbertSmithPaper.Corner.RoundSphere

/-!
# The exterior

For `n ≥ 1` and `R > 0`, the exterior is `Z₀ = {∞} ∪ {z ∈ ℝ^n : |z| ≥ R} ⊆ S^n` in the round sphere.

Lean encoding. `HSP.Corner.exterior n R` takes only `n` and `R`; the conditions `n ≥ 1` and `R > 0`
are not needed to form the set. For a compact metric space `T` with an isometric `C_p`-action,
possibly empty, `Z = T × Z₀` is `(Set.univ : Set T) ×ˢ exterior n R`, with no separate
declaration: Mathlib's product metric on `T × S^n` is the maximum metric `max(d_T, d_S)`, and
Mathlib's product action of `C_p` on `T × S^n` is the action on the first factor, since `C_p` acts
trivially on `S^n`.
-/

namespace HSP.Corner

/-- The *exterior* `Z₀ = {∞} ∪ {z ∈ ℝ^n : |z| ≥ R}` in the round sphere `S^n`. -/
def exterior (n : ℕ) (R : ℝ) : Set (RoundSphere n) :=
  insert OnePoint.infty
    (((↑) : EuclideanSpace ℝ (Fin n) → RoundSphere n) '' {z | R ≤ ‖z‖})

end HSP.Corner
