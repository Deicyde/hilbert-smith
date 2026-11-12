import Mathlib

/-!
# Representatives of the finite quotients

`r_i : ℤ/p^i → ℤ_p` sends a residue class to its representative in `{0, …, p^i - 1}`
(`ZMod.val`), viewed as a `p`-adic integer. The finite quotient `ℤ/p^i` is Mathlib's
`ZMod (p ^ i)`. The definition is stated for every `i ∈ ℕ`; for `i = 0` it is the zero map.
-/

namespace HSP

/-- The representative map `r_i : ZMod (p ^ i) → ℤ_[p]`, `g ↦ g.val`, the representative of `g`
in `{0, …, p^i - 1}`. -/
noncomputable def rep (p : ℕ) [Fact p.Prime] (i : ℕ) (g : ZMod (p ^ i)) : ℤ_[p] :=
  (g.val : ℤ_[p])

end HSP
