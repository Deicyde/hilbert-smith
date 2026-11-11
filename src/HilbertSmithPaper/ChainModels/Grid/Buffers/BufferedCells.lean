import Mathlib
import HilbertSmithPaper.ChainModels.Grid.SphereLabels

/-!
# Buffered cells

The buffered cells `𝓑_i(v)` are the cells `b` of `D_i`, and their duals in `D_i^{N-*}`, whose
sphere label lies in the open Euclidean ball `B(0, v) ⊆ ℝⁿ ⊆ Sⁿ`; membership depends on `s_b`
alone. More generally, for any finite set of cells `B` with torus labels `x_b`,
`𝓑(v) = {b : f_T(x_b) ∈ B(0, v)}`.

## Encoding

`IsBufferedLabel v s` says `s ∈ B(0, v)`, i.e. `s` is a point of `ℝⁿ` of norm `< v`.
`bufferedCells A ρ x v` (the declaration of the article) is `𝓑(v)` for cells with torus labels
`x : B → 𝕋ⁿ` and the torus test map `f_T` of radius `ρ`. For `D_i` in degree `r`, `x` is
`chainModelLabel A i r` (then `f_T(x_b)` is the sphere label), and for the dual cells of
`(D_i^{N-*})_r` it is `chainModelDualLabel A i r`.
-/

namespace HSP.ChainModels

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- A sphere label `s` is *buffered* at radius `v` if `s ∈ B(0, v)`, the open Euclidean ball in
`ℝⁿ ⊆ Sⁿ`. -/
def IsBufferedLabel (v : ℝ) (s : Corner.RoundSphere n) : Prop :=
  s ∈ ((↑) '' Metric.ball (0 : EuclideanSpace ℝ (Fin n)) v :
    Set (OnePoint (EuclideanSpace ℝ (Fin n))))

/-- The *buffered cells* `𝓑(v)` of a set of cells `B` with torus labels `x`: those with
`f_T(x_b) ∈ B(0, v)`; for the cells of `D_i` (and their duals) these are `𝓑_i(v)`. -/
def bufferedCells (A : LocalDatum p n D ρplus) (ρ : ℝ) {B : Type*} (x : B → Torus n) (v : ℝ) :
    Set B :=
  {b | IsBufferedLabel v (torusTestMap A ρ (x b) : Corner.RoundSphere n)}

end HSP.ChainModels
