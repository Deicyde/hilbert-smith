import HilbertSmithPaper.Categories.Asymptotic.Restriction.RestrictionIndexEmbedding

/-!
# Enumerated indices satisfy the predicate

Every index `M.restrictEmb P i k` enumerated by the sub-basis enumeration satisfies `P i`.
-/

open CategoryTheory CategoryTheory.Limits Filter Topology

namespace HSP

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

namespace AsymPre

variable (M : AsymPre G X) (P : ∀ i, Fin (M.n i) → Prop)

variable {M P}

omit [MetricSpace X] [AddAction (ZMod p) X] in
open scoped Classical in
/-- The enumerated indices satisfy `P`. -/
theorem restrictEmb_mem {i : ℕ} (k : Fin (Finset.univ.filter (P i)).card) :
    P i (M.restrictEmb P i k) :=
  (Finset.mem_filter.1 (Finset.orderEmbOfFin_mem (Finset.univ.filter (P i)) rfl k)).2

end AsymPre

end HSP
