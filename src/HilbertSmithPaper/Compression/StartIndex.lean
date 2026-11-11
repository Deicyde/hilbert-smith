import Mathlib
import HilbertSmithPaper.Compression.BufferEventually

/-!
# Start index and bound sequence

With the null sequence `(ε'_i)` chosen in "buffers hold eventually", the start index `i₀ ≥ 1` is
the least index such that items (1)-(3) of that lemma hold with `(ε'_i)` for every `i ≥ i₀`. The
bound sequence is `δ_i = ε'_i` for `i ≥ i₀` and `δ_i = 0` for `i < i₀`; it is a null sequence.

## Encoding

* `bufferBound F` is the chosen `(ε'_i)` (`Exists.choose` of `buffer_eventually`).
* `startIndex F` (the declaration of the article) is `Nat.find` of the existence of an index
  `i₀ ≥ 1` with `BuffersHold F (bufferBound F) i` for all `i ≥ i₀`; `bound F` is `δ`.
-/

open Filter Topology

namespace HSP.Compression

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The null sequence `(ε'_i)` chosen in "buffers hold eventually". -/
noncomputable def bufferBound (F : FixedLocalData p n D ρplus) : ℕ → ℝ :=
  (buffer_eventually F).choose

lemma bufferBound_spec (F : FixedLocalData p n D ρplus) :
    Tendsto (bufferBound F) atTop (𝓝 0) ∧ ∀ᶠ i in atTop, BuffersHold F (bufferBound F) i :=
  (buffer_eventually F).choose_spec

/-- Some `i₀ ≥ 1` has items (1)-(3) with `(ε'_i)` for every `i ≥ i₀`. -/
private lemma exists_startIndex (F : FixedLocalData p n D ρplus) :
    ∃ i₀ : ℕ, 1 ≤ i₀ ∧ ∀ i ≥ i₀, BuffersHold F (bufferBound F) i := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (bufferBound_spec F).2
  exact ⟨max N 1, le_max_right _ _, fun i hi => hN i ((le_max_left _ _).trans hi)⟩

open Classical in
/-- The *start index* `i₀ ≥ 1`: the least index such that items (1)-(3) of "buffers hold
eventually" hold with `(ε'_i)` for every `i ≥ i₀`. -/
noncomputable def startIndex (F : FixedLocalData p n D ρplus) : ℕ :=
  Nat.find (exists_startIndex F)

lemma startIndex_spec (F : FixedLocalData p n D ρplus) :
    1 ≤ startIndex F ∧ ∀ i ≥ startIndex F, BuffersHold F (bufferBound F) i := by
  classical
  exact Nat.find_spec (exists_startIndex F)

open Classical in
/-- The *bound sequence* `δ_i = ε'_i` for `i ≥ i₀` and `δ_i = 0` for `i < i₀`. -/
noncomputable def bound (F : FixedLocalData p n D ρplus) (i : ℕ) : ℝ :=
  if startIndex F ≤ i then bufferBound F i else 0

/-- The bound sequence is a null sequence. -/
lemma bound_tendsto (F : FixedLocalData p n D ρplus) : Tendsto (bound F) atTop (𝓝 0) := by
  refine (bufferBound_spec F).1.congr' ?_
  filter_upwards [eventually_ge_atTop (startIndex F)] with i hi
  simp [bound, hi]

end HSP.Compression
