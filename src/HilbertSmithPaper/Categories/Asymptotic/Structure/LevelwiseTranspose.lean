import Mathlib
import HilbertSmithPaper.Categories.Asymptotic.Structure.MorphismPropagation
import HilbertSmithPaper.Categories.Asymptotic.PropTranspose

/-!
# The levelwise transpose

For a sequence `u = (u_i)` of matrices `M → N` of the asymptotic category, the levelwise
transpose `(u_iᵀ)` is a sequence `N → M` with the same propagation (`HSP.AsymPre.transpose`).
-/

open CategoryTheory Filter

namespace HSP

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

namespace AsymPre

/-- The levelwise transpose `(u_iᵀ)` of a sequence of matrices. -/
def transpose {M N : AsymPre G X} (u : M ⟶ N) : N ⟶ M :=
  homMk (fun i => DualCat.dualHom (coord u i)) (by
    refine (tendsto_congr fun i => ?_).2 (tendsto_prop u)
    exact prop_transpose (M.label i) (N.label i) (FreeCat.mat (coord u i)))

@[simp] theorem coord_transpose {M N : AsymPre G X} (u : M ⟶ N) (i : ℕ) :
    coord (transpose u) i = DualCat.dualHom (coord u i) := rfl

end AsymPre

end HSP
