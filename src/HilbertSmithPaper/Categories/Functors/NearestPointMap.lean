import Mathlib

/-!
# Nearest-point maps

If `S` is a nonempty closed subset of a compact metric space `X`, there is a map `ρ : X → S` with
`d(x, ρ x) = d(x, S)` for every `x`: `S` is compact, so the distance from `x` to `S` is attained
(`IsCompact.exists_infDist_eq_dist`), and `ρ x` is a chosen point where it is attained. Such a
`ρ` is the input of the relabelling equivalence (`HSP.relabelEquiv`).
-/

namespace HSP

/-- **Nearest-point maps.** A nonempty closed subset `S` of a compact metric space `X` has a map
`ρ : X → S` with `d(x, ρ x) = d(x, S)` for every `x`. -/
theorem exists_nearestPoint {X : Type*} [MetricSpace X] [CompactSpace X] {S : Set X}
    (hS : IsClosed S) (hne : S.Nonempty) :
    ∃ ρ : X → S, ∀ x, dist x (ρ x : X) = Metric.infDist x S := by
  have h := fun x => hS.isCompact.exists_infDist_eq_dist hne x
  exact ⟨fun x => ⟨(h x).choose, (h x).choose_spec.1⟩, fun x => (h x).choose_spec.2.symm⟩

end HSP
