import Mathlib
import HilbertSmithPaper.Compression.BoundSequence

/-!
# The bound sequence is null

The bound sequence `δ` tends to `0`: it agrees with the null sequence `(ε'_i)` from the start
index on.
-/

open Filter Topology

namespace HSP.Compression

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- **The bound sequence is null.** -/
lemma bound_tendsto (F : FixedLocalData p n D ρplus) : Tendsto (bound F) atTop (𝓝 0) := by
  refine (buffer_eventually F).choose_spec.1.congr' ?_
  filter_upwards [eventually_ge_atTop (startIndex F)] with i hi
  simp [bound, hi]

end HSP.Compression
