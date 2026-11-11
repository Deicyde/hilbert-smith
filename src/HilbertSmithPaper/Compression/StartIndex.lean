import Mathlib
import HilbertSmithPaper.Compression.BufferConditions
import HilbertSmithPaper.Compression.BufferEventually

/-!
# Start index

With the null sequence `(ε'_i)` chosen in "buffers hold eventually", the start index `i₀ ≥ 1` is
the least index such that the buffer conditions hold with `(ε'_i)` for every `i ≥ i₀`.

## Encoding

* The chosen `(ε'_i)` is `(buffer_eventually F).choose`.
* `startIndex F` (the declaration of the article) is `Nat.find` of the existence of an index
  `i₀ ≥ 1` with `BuffersHold F (buffer_eventually F).choose i` for all `i ≥ i₀`;
  `startIndex_spec` records its defining property.
-/

open Filter Topology

namespace HSP.Compression

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- Some `i₀ ≥ 1` has the buffer conditions with `(ε'_i)` for every `i ≥ i₀`. -/
private lemma exists_startIndex (F : FixedLocalData p n D ρplus) :
    ∃ i₀ : ℕ, 1 ≤ i₀ ∧ ∀ i ≥ i₀, BuffersHold F (buffer_eventually F).choose i := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (buffer_eventually F).choose_spec.2.2
  exact ⟨max N 1, le_max_right _ _, fun i hi => hN i ((le_max_left _ _).trans hi)⟩

open Classical in
/-- The *start index* `i₀ ≥ 1`: the least index such that the buffer conditions hold with the
chosen `(ε'_i)` for every `i ≥ i₀`. -/
noncomputable def startIndex (F : FixedLocalData p n D ρplus) : ℕ :=
  Nat.find (exists_startIndex F)

lemma startIndex_spec (F : FixedLocalData p n D ρplus) :
    1 ≤ startIndex F ∧ ∀ i ≥ startIndex F, BuffersHold F (buffer_eventually F).choose i := by
  classical
  exact Nat.find_spec (exists_startIndex F)

end HSP.Compression
