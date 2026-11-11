import Mathlib
import HilbertSmithPaper.Compression.BufferConditions
import HilbertSmithPaper.ChainModels.Grid.ChainModelEstimates

/-!
# Buffers hold eventually

For fixed local data there are `i₁` and a null sequence `(ε'_i)` of nonnegative reals such that
the buffer conditions
hold with `(ε'_i)` for every `i ≥ i₁`.

## Encoding

`buffer_eventually` (the declaration of the article) asserts a nonnegative null sequence `ε'` with
`BuffersHold F ε' i` for all large `i` (`∀ᶠ i in atTop`, which is "there is `i₁` such that for
every `i ≥ i₁`").
-/

open Filter Topology

namespace HSP.Compression

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- **Buffers hold eventually.** There are an index `i₁` and a null sequence `(ε'_i)` of
nonnegative reals such that
the buffer conditions hold with `(ε'_i)` for every `i ≥ i₁`. -/
theorem buffer_eventually (F : FixedLocalData p n D ρplus) :
    ∃ ε' : ℕ → ℝ, Tendsto ε' atTop (𝓝 0) ∧ (∀ i, 0 ≤ ε' i) ∧
      ∀ᶠ i in atTop, BuffersHold F ε' i := by
  sorry

end HSP.Compression
