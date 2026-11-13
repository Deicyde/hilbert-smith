import Mathlib

/-!
# Closed arcs of the circle

A closed arc of `ℝ/4ℤ` is `circleArc a ℓ`, the image of `[a, a + ℓ]`, `ℓ ≥ 0`.
`shortestArc Y` is a closed arc containing `Y` of least length (a choice); if no arc of least
length exists it is the whole circle.
-/

namespace HSP.ChainModels

/-- The closed arc of `ℝ/4ℤ` from `a` to `a + ℓ`. -/
def circleArc (a ℓ : ℝ) : Set (AddCircle (4 : ℝ)) :=
  (fun t : ℝ => (t : AddCircle (4 : ℝ))) '' Set.Icc a (a + ℓ)

open Classical in
/-- A shortest closed arc `J` containing `Y`. -/
noncomputable def shortestArc (Y : Set (AddCircle (4 : ℝ))) : Set (AddCircle (4 : ℝ)) :=
  if h : ∃ q : ℝ × ℝ, 0 ≤ q.2 ∧ Y ⊆ circleArc q.1 q.2 ∧
      ∀ q' : ℝ × ℝ, 0 ≤ q'.2 → Y ⊆ circleArc q'.1 q'.2 → q.2 ≤ q'.2 then
    circleArc h.choose.1 h.choose.2
  else Set.univ

end HSP.ChainModels
