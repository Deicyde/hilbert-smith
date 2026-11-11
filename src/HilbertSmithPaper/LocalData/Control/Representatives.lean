import Mathlib
import HilbertSmithPaper.LocalData.Chart.LocalDatum
import HilbertSmithPaper.LocalData.Control.RepresentativesAlgebra
import HilbertSmithPaper.LocalData.Subgroups.SmallDisplacement
import HilbertSmithPaper.LocalData.Subgroups.PadicSubgroupsBasis

/-!
# Representatives act approximately

For a compact `ℤ_[p]`-invariant `C ⊆ Ω` and `ε > 0` there is `L ≥ 1` with
`|r_i g +ᵥ (r_i g' +ᵥ x) - r_i (g + g') +ᵥ x| < ε` for all `i ≥ L`, `g, g' ∈ ZMod (p ^ i)` and
`x ∈ C`. Small displacement for the inclusion of `Ω` into `ℝⁿ` gives a neighbourhood `V` of `0`, the
basis property an `H_L ⊆ V`; the left point is `k +ᵥ y` with `y = r_i (g + g') +ᵥ x ∈ C` and
`k ∈ H_i ⊆ H_L`.
-/

open Topology

namespace HSP

/-- Representatives of `ZMod (p ^ i)` act on a compact invariant set as a group action up to an
error that tends to `0` with `i`, uniformly. -/
theorem LocalDatum.rep_vadd_close {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}
    (A : LocalDatum p n D ρplus) {C : Set A.Ω} (hC : IsCompact C)
    (hCinv : ∀ a : ℤ_[p], ∀ x ∈ C, a +ᵥ x ∈ C) {ε : ℝ} (hε : 0 < ε) :
    ∃ L ≥ 1, ∀ i ≥ L, ∀ g g' : ZMod (p ^ i), ∀ x ∈ C,
      dist ((rep p i g +ᵥ (rep p i g' +ᵥ x) : A.Ω) : EuclideanSpace ℝ (Fin n))
        ((rep p i (g + g') +ᵥ x : A.Ω) : EuclideanSpace ℝ (Fin n)) < ε := by
  have : Nonempty A.Ω := ⟨⟨0, A.ball_subset (by simp)⟩⟩
  let e := (A.isOpen_Ω.isOpenEmbedding_subtypeVal).toOpenPartialHomeomorph
  obtain ⟨V, hV, hVd⟩ := exists_nhds_zero_small_displacement (G := ℤ_[p]) e hC
    (by simp [e]) hε
  obtain ⟨L, hL⟩ := (padicSubgroup_basis p).2.2 V hV
  refine ⟨max L 1, le_max_right _ _, fun i hi g g' x hx => ?_⟩
  have hk := (rep_spec p (le_of_max_le_right hi) g g').2.2.1
  have hkV : rep p i g + rep p i g' - rep p i (g + g') ∈ V :=
    hL (dvd_trans (pow_dvd_pow _ (le_of_max_le_left hi)) hk)
  have hy := hCinv (rep p i (g + g')) x hx
  have h := (hVd _ hkV _ hy).2
  rw [vadd_vadd, sub_add_cancel, ← vadd_vadd] at h
  simpa [e] using h

end HSP
