import Mathlib
import HilbertSmithPaper.Categories.Asymptotic.AsymptoticCategory

/-!
# Morphisms have propagation tending to zero

The matrices `u_i` of a morphism `u : M → N` of sequences have `prop(u_i) → 0` for the labels of
`M` and `N` (`HSP.AsymPre.tendsto_prop`).
-/

open CategoryTheory CategoryTheory.Limits Filter Topology
open scoped NNReal

namespace HSP

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

/-- The matrices of a morphism have propagation tending to `0`. -/
theorem AsymPre.tendsto_prop {M N : AsymPre G X} (u : M ⟶ N) :
    Tendsto (fun i => prop (M.label i) (N.label i) (FreeCat.mat (AsymPre.coord u i))) atTop
      (𝓝 0) :=
  u.2

end HSP
