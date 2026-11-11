import Mathlib

/-!
# Local exclusion

No faithful jointly continuous action of `ℤ_[p]` on a nonempty connected open set
`O ⊆ ℝⁿ` (`IsOpen O`, `IsConnected O`). The action is an `AddAction` on the subtype `O`, the
same form as the conclusion of `HSP.oneChart`.

The statement is in place; its proof is still `sorry`.
-/

namespace HSP

/-- **Local exclusion.** For a prime `p` and a nonempty connected open set `O ⊆ ℝⁿ`, no jointly
continuous action of `ℤ_[p]` on `O` is faithful. -/
theorem localExclusion (p : ℕ) [Fact p.Prime] (n : ℕ) (O : Set (EuclideanSpace ℝ (Fin n)))
    (hO : IsOpen O) (hc : IsConnected O) [AddAction ℤ_[p] O] [ContinuousVAdd ℤ_[p] O] :
    ¬ FaithfulVAdd ℤ_[p] O := by
  sorry

end HSP
