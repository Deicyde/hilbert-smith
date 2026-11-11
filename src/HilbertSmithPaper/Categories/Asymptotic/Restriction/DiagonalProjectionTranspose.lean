import HilbertSmithPaper.Categories.Asymptotic.Restriction.DiagonalProjection
import HilbertSmithPaper.Categories.Asymptotic.AsymptoticDuality

/-!
# Diagonal projections are self-transpose

The diagonal coordinate projection `trunc P` is its own transpose.
-/

open CategoryTheory CategoryTheory.Limits Filter Topology

namespace HSP

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

namespace AsymPre

variable (M : AsymPre G X) (P : ∀ i, Fin (M.n i) → Prop)

variable [∀ i, DecidablePred (P i)]

/-- `(trunc P)ᵀ = trunc P`. -/
theorem transpose_trunc : transpose (M.trunc P) = M.trunc P :=
  hom_ext fun _ => FreeCat.hom_ext (by exact Matrix.diagonal_transpose _)

end AsymPre

end HSP
