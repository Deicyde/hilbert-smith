import Mathlib

/-!
# Newman's theorem: small orbits

A classical input, stated over Mathlib notions with a `sorry` proof (an open statement). The chart
is an `OpenPartialHomeomorph` from `M` to `EuclideanSpace ℝ (Fin n)` whose target contains the
closed unit ball. The set of points of the domain mapped into `S ⊆ target` is written
`e.symm '' S` (never the raw preimage `e ⁻¹' S`, which also contains points outside the source).
The displacement hypothesis is on the whole cyclic orbit (`g^[k]` for every `k`). `δ` is chosen
before the prime `q` and the homeomorphism `g`.
-/

namespace HSP

/-- **Newman's theorem, small orbits** (classical, open statement). For a chart `e` of a space
`M` whose target contains the closed unit ball, there is `δ > 0` such that every homeomorphism
`g` of prime order `q` whose orbits from the closed chart ball stay in the chart and move by less
than `δ` in coordinates fixes the open chart ball pointwise. -/
theorem newman_small_orbits {n : ℕ} {M : Type*} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (he : Metric.closedBall 0 1 ⊆ e.target) :
    ∃ δ > 0, ∀ q : ℕ, q.Prime → ∀ g : M ≃ₜ M, (∀ x, (⇑g)^[q] x = x) →
      (∀ k : ℕ, ∀ x ∈ e.symm '' Metric.closedBall 0 1,
        (⇑g)^[k] x ∈ e.source ∧ dist (e ((⇑g)^[k] x)) (e x) < δ) →
      ∀ x ∈ e.symm '' Metric.ball 0 1, g x = x := by
  sorry

end HSP
