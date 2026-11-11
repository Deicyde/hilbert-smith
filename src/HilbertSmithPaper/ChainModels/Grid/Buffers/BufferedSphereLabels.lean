import Mathlib
import HilbertSmithPaper.Corner.RoundSphere

/-!
# Buffered sphere labels

A sphere label `s ∈ Sⁿ` is buffered at radius `v` if `s ∈ B(0, v)`, the open Euclidean ball in
`ℝⁿ ⊆ Sⁿ`.

## Encoding

`IsBufferedLabel v s` (the declaration of the article) says `s` is the image in the one-point
compactification of a point of `ℝⁿ` of norm `< v`.
-/

namespace HSP.ChainModels

variable {n : ℕ}

/-- A sphere label `s` is *buffered* at radius `v` if `s ∈ B(0, v)`, the open Euclidean ball in
`ℝⁿ ⊆ Sⁿ`. -/
def IsBufferedLabel (v : ℝ) (s : Corner.RoundSphere n) : Prop :=
  s ∈ ((↑) '' Metric.ball (0 : EuclideanSpace ℝ (Fin n)) v :
    Set (OnePoint (EuclideanSpace ℝ (Fin n))))

end HSP.ChainModels
