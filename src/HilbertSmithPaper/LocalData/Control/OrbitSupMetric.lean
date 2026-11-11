import Mathlib
import HilbertSmithPaper.LocalData.Chart.TestRegion

/-!
# The orbit sup-distance on the test region

For a local datum, `d₁ z w = max_{a ∈ ℤ_p} |a +ᵥ z - a +ᵥ w|` for `z, w ∈ Z⁺`, computed with the
action on `Ω`. It is written as a supremum; the supremum is attained (`ℤ_[p]` is compact and the
action continuous), so it is the maximum of the article.
-/

namespace HSP

/-- The orbit sup-distance `d₁ z w = sup_a |a +ᵥ z - a +ᵥ w|` on the test region. -/
noncomputable def LocalDatum.d₁ {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}
    (A : LocalDatum p n D ρplus) (z w : A.Zplus) : ℝ :=
  ⨆ a : ℤ_[p], dist ((a +ᵥ (z : A.Ω) : A.Ω) : EuclideanSpace ℝ (Fin n))
    ((a +ᵥ (w : A.Ω) : A.Ω) : EuclideanSpace ℝ (Fin n))

end HSP
