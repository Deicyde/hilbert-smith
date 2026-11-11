import Mathlib

/-!
# Intrinsic interior

The intrinsic interior `intrinsicInterior n M` of a topological space `M`: the points having an
open neighbourhood homeomorphic to an open subset of `ℝⁿ`. A homeomorphism from an open subset
of `M` onto an open subset of `ℝⁿ` is an `OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))`
(its source and target are open by definition). No atlas of `M` is used; in particular this is
not Mathlib's `ModelWithCorners.interior`, which depends on the chosen charts.
-/

namespace HSP

/-- The *intrinsic interior* `M°ₙ` of `M`: the set of points `x` lying in the domain of some
homeomorphism from an open subset of `M` onto an open subset of `ℝⁿ`. -/
def intrinsicInterior (n : ℕ) (M : Type*) [TopologicalSpace M] : Set M :=
  {x | ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)), x ∈ e.source}

end HSP
