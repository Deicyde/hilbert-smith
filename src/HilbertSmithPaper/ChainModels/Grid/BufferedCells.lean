import Mathlib
import HilbertSmithPaper.ChainModels.Grid.SphereLabels

/-!
# Buffered cells

The buffered cells `𝓑_i(v)` are the cells `b` of `D_i`, and their duals in `D_i^{N-*}`, whose
sphere label lies in the open Euclidean ball `B(0, v) ⊆ ℝⁿ ⊆ Sⁿ`; membership depends on `s_b`
alone.

## Encoding

`IsBufferedLabel v s` says `s ∈ B(0, v)`, i.e. `s` is a point of `ℝⁿ` of norm `< v`.
`bufferedCells A ρ i r v` (the declaration of the article) is the set of buffered basis cells of
`(D_i)_r`, `bufferedDualCells` that of buffered dual cells of `(D_i^{N-*})_r`.
-/

namespace HSP.ChainModels

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- A sphere label `s` is *buffered* at radius `v` if `s ∈ B(0, v)`, the open Euclidean ball in
`ℝⁿ ⊆ Sⁿ`. -/
def IsBufferedLabel (v : ℝ) (s : Corner.RoundSphere n) : Prop :=
  s ∈ ((↑) '' Metric.ball (0 : EuclideanSpace ℝ (Fin n)) v :
    Set (OnePoint (EuclideanSpace ℝ (Fin n))))

/-- The *buffered cells* `𝓑_i(v)` of `(D_i)_r`: the basis cells whose sphere label lies in
`B(0, v)`. -/
def bufferedCells (A : LocalDatum p n D ρplus) (ρ : ℝ) (i : ℕ) (r : ℤ) (v : ℝ) :
    Set (Fin ((chainModel A i).X r).dim) :=
  {a | IsBufferedLabel v (sphereLabel A ρ i r a)}

/-- The buffered dual cells of `(D_i^{N-*})_r`. -/
def bufferedDualCells (A : LocalDatum p n D ρplus) (ρ : ℝ) (i : ℕ) (r : ℤ) (v : ℝ) :
    Set (Fin ((chainModel A i).X ((n + 4 : ℕ) - r)).dim) :=
  {a | IsBufferedLabel v (dualSphereLabel A ρ i r a)}

end HSP.ChainModels
