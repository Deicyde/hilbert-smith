import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.Homeomorph.Defs

/-!
# The published inputs of OpenAI's route

OpenAI's preprint *The Hilbert–Smith conjecture in every finite dimension* cites a few published
theorems instead of proving them. This file states each of them as a `Prop`, so that the route can
take it as an explicit hypothesis, as HS_proof's `HSFormal` did with its own inputs before proving
them. The file imports Mathlib only.

* `HilbertSmith.NewmanInput`: Newman's theorem in the form used in the proof of Proposition 5.1
  (an invariant chart subset).

## References

* M. H. A. Newman, *A theorem on periodic transformations of spaces*, Quart. J. Math. 2 (1931),
  1–8.
* J. Pardon, *The Hilbert–Smith conjecture for three-manifolds*, J. Amer. Math. Soc. 26 (2013),
  879–899; §4.1 has the same local reduction.
* J. Pardon, *Totally disconnected groups (not) acting on two-manifolds*, in *Breadth in
  Contemporary Topology*, Proc. Sympos. Pure Math. 102 (2019); author manuscript pp. 2–3 give a
  modern statement and proof of Newman's theorem.
-/

namespace HilbertSmith

universe u

/-- **Newman's theorem**, in the form OpenAI's proof of Proposition 5.1 uses it: a finite-order
homeomorphism of a connected (Hausdorff, topological) manifold without boundary which is the
identity on a nonempty open subset is the identity everywhere.

OpenAI states it in this form, citing [Newman 1931] and [Pardon 2019, pp. 2–3], at the start of the
proof of Proposition 5.1 (`prop:chart-reduction`). There it is applied to the periodic
homeomorphisms of the saturation `N' = H_j B` of a coordinate ball, through which the action of
`H_j` factors via a finite quotient.

No second countability is assumed, as in OpenAI's text. The finite order is written `f^[k] = id`
for some `k > 0`. -/
def NewmanInput : Prop :=
  ∀ (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [ConnectedSpace M] (f : M ≃ₜ M) (k : ℕ),
    0 < k → (∀ x, f^[k] x = x) → ∀ U : Set M, IsOpen U → U.Nonempty → (∀ x ∈ U, f x = x) →
      ∀ x, f x = x

end HilbertSmith
