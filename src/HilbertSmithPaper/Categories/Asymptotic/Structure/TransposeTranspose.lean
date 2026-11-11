import Mathlib
import HilbertSmithPaper.Categories.Asymptotic.Structure.LevelwiseTranspose

/-!
# Transposing twice

The levelwise transpose of the levelwise transpose of a sequence `u` is `u`
(`HSP.AsymPre.transpose_transpose`).
-/

open CategoryTheory

namespace HSP

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

/-- `(uᵀ)ᵀ = u` for sequences of matrices. -/
theorem AsymPre.transpose_transpose {M N : AsymPre G X} (u : M ⟶ N) :
    AsymPre.transpose (AsymPre.transpose u) = u :=
  AsymPre.hom_ext fun i =>
    FreeCat.hom_ext (Matrix.transpose_transpose (FreeCat.mat (AsymPre.coord u i)))

end HSP
