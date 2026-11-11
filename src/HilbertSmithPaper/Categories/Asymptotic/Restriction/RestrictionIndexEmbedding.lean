import HilbertSmithPaper.Categories.Asymptotic.AsymptoticCategory

/-!
# Enumeration of a sub-basis

For a predicate `P i k` on the indices of `M = (n_i, x_i)`, `M.restrictEmb P i` is the increasing
enumeration `Fin m_i ↪o Fin n_i` of the indices `k` with `P i k`, where `m_i` is their number
(`P` is decided classically).
-/

open CategoryTheory CategoryTheory.Limits Filter Topology

namespace HSP

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

namespace AsymPre

variable (M : AsymPre G X) (P : ∀ i, Fin (M.n i) → Prop)

open scoped Classical in
/-- The increasing enumeration of the indices `k` with `P i k`. -/
noncomputable def restrictEmb (i : ℕ) : Fin (Finset.univ.filter (P i)).card ↪o Fin (M.n i) :=
  (Finset.univ.filter (P i)).orderEmbOfFin rfl

end AsymPre

end HSP
