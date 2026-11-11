import HilbertSmithPaper.Categories.Asymptotic.Restriction.CoordinateInclusion
import HilbertSmithPaper.Categories.Asymptotic.AsymptoticDuality

/-!
# Coordinate projection onto a restriction

The coordinate projection `M → M_P` of a restriction is the transpose of the coordinate inclusion.
-/

open CategoryTheory CategoryTheory.Limits Filter Topology

namespace HSP

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

namespace AsymPre

variable (M : AsymPre G X) (P : ∀ i, Fin (M.n i) → Prop)

/-- The coordinate projection `M → M_P`, the transpose of the inclusion. -/
noncomputable def restrictPro : M ⟶ M.restrict P := transpose (M.restrictInc P)

theorem mat_restrictPro (i : ℕ) :
    FreeCat.mat (coord (M.restrictPro P) i) = (FreeCat.inclMat (M.restrictEmb P i)).transpose :=
  rfl

end AsymPre

end HSP
