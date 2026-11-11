import Mathlib

/-!
# Propagation

For finite sets `B, B'` with labels `l : B → X`, `l' : B' → X` in a metric space `X` and a rational
matrix `u ∈ ℚ^{B' × B}`, the propagation of `u` is the largest distance `d(l' b', l b)` over the
nonzero entries `u b' b`, and `0` when `u = 0`.

Lean encoding: the value lies in `ℝ≥0` and is a `Finset.sup` over the pairs `(b', b)` with
`u b' b ≠ 0`, so that the empty maximum is `0` automatically. (Labels are written `l`, `l'`, since
`λ` is a keyword.)
-/

open scoped NNReal

namespace HSP

variable {X : Type*} [MetricSpace X] {B B' : Type*} [Fintype B] [Fintype B']

/-- The *propagation* `prop(u) = max {d(l' b', l b) : u b' b ≠ 0}` of a rational matrix
`u ∈ ℚ^{B' × B}` with labels `l : B → X` on its source and `l' : B' → X` on its target;
it is `0` when `u = 0`. -/
noncomputable def prop (l : B → X) (l' : B' → X) (u : Matrix B' B ℚ) : ℝ≥0 :=
  (Finset.univ.filter fun q : B' × B => u q.1 q.2 ≠ 0).sup fun q => nndist (l' q.1) (l q.2)

end HSP
