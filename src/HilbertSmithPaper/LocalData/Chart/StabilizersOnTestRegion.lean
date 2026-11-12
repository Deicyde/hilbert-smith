import Mathlib
import HilbertSmithPaper.LocalData.Chart.TestRegionNotFixed
import HilbertSmithPaper.LocalData.Subgroups.ProperClosedSubgroups

/-!
# Stabilizers on the test region

For `z ∈ Z⁺`, the stabilizer of `z` is a closed subgroup of `ℤ_[p]` (the action is continuous and
`Ω` is Hausdorff), and it is not all of `ℤ_[p]` since `z` is moved; so it lies in `H_1`.
-/

namespace HSP

/-- The stabilizer of a point of the test region lies in `H_1`. -/
theorem LocalDatum.stabilizer_le {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}
    (A : LocalDatum p n D ρplus) {z : A.Ω} (hz : z ∈ A.Zplus) :
    AddAction.stabilizer ℤ_[p] z ≤ padicSubgroup p 1 := by
  refine le_padicSubgroup_one_of_ne_top ?_ ?_
  · exact isClosed_eq (continuous_id.vadd continuous_const) continuous_const
  · intro htop
    obtain ⟨a, ha⟩ := A.exists_moved_of_mem_Zplus hz
    have : a ∈ AddAction.stabilizer ℤ_[p] z := htop ▸ AddSubgroup.mem_top a
    exact ha this

end HSP
