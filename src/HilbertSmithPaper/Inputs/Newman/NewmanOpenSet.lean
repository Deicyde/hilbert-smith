import Mathlib

/-!
# Newman's theorem: fixing an open set

A classical input, stated over Mathlib notions with a `sorry` proof (an open statement). A
connected `n`-manifold is a connected Hausdorff space charted on `EuclideanSpace ℝ (Fin n)`, with
no countability assumption. Periodicity is `f^[k] = id` for some `k ≥ 1`.
-/

namespace HSP

/-- **Newman's theorem, fixing an open set** (classical, open statement). A periodic homeomorphism
of a connected `n`-manifold that fixes every point of a nonempty open set is the identity. -/
theorem newman_open_set {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (f : M ≃ₜ M) (k : ℕ) (hk : 1 ≤ k)
    (hper : (⇑f)^[k] = id) (U : Set M) (hU : IsOpen U) (hUne : U.Nonempty)
    (hfix : ∀ x ∈ U, f x = x) : ⇑f = id := by
  sorry

end HSP
