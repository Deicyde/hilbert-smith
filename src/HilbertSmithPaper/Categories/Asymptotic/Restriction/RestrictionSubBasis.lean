import HilbertSmithPaper.Categories.Asymptotic.Restriction.RestrictionIndexEmbedding

/-!
# Restriction to a sub-basis

For a predicate `P i k` on the indices of `M = (n_i, x_i)`, `M.restrict P` (`M_P`) keeps the indices
`k` with `P i k`, in increasing order (`HSP.AsymPre.restrictEmb`), with their labels.
-/

open CategoryTheory CategoryTheory.Limits Filter Topology

namespace HSP

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

namespace AsymPre

variable (M : AsymPre G X) (P : ∀ i, Fin (M.n i) → Prop)

open scoped Classical in
/-- The restriction `M_P`: the indices `k` with `P i k`, with their labels. -/
noncomputable def restrict : AsymPre G X where
  n i := (Finset.univ.filter (P i)).card
  x i k := M.x i (M.restrictEmb P i k)

omit [MetricSpace X] [AddAction (ZMod p) X] in
@[simp] theorem restrict_x (i : ℕ) (k : Fin ((M.restrict P).n i)) :
    (M.restrict P).x i k = M.x i (M.restrictEmb P i k) := rfl

end AsymPre

end HSP
