import Mathlib

/-!
# Integer tails

A sequence of integers cannot both be eventually `±1` and eventually divisible by `p > 1`: at an
index beyond both thresholds, `p ∣ ±1`, so `p = 1`.
-/

open Filter

namespace HSP

/-- For a natural number `p > 1` and a sequence `s` of integers, it is impossible both that
`s i ∈ {1, -1}` for all large `i` and that `p ∣ s i` for all large `i`. -/
theorem not_eventually_unit_and_dvd {p : ℕ} (hp : 1 < p) (s : ℕ → ℤ) :
    ¬ ((∀ᶠ i in atTop, s i = 1 ∨ s i = -1) ∧ ∀ᶠ i in atTop, (p : ℤ) ∣ s i) := by
  rintro ⟨h1, h2⟩
  obtain ⟨i, hi, hdvd⟩ := (h1.and h2).exists
  have hp1 : (p : ℤ) ∣ 1 := by
    rcases hi with hi | hi <;> rw [hi] at hdvd
    · exact hdvd
    · exact dvd_neg.1 hdvd
  have : p = 1 := Nat.dvd_one.1 (Int.natCast_dvd_natCast.1 (by simpa using hp1))
  omega

end HSP
