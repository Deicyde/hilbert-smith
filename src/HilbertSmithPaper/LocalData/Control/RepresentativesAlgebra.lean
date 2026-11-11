import Mathlib
import HilbertSmithPaper.LocalData.Control.RepresentativeMap
import HilbertSmithPaper.LocalData.Control.ReductionKernel

/-!
# Algebra of the representatives

For `i ≥ 1`, with `q_i = PadicInt.toZModPow i`, `χ_i = ZMod.castHom _ (ZMod p)` and
`q_1 = PadicInt.toZMod`, and all `g, g' ∈ ZMod (p ^ i)`:
`q_i (r_i g) = g`, `r_i 0 = 0`, `r_i g + r_i g' - r_i (g + g') ∈ H_i`, and `χ_i g = q_1 (r_i g)`.
-/

namespace HSP

/-- The representatives are a section of reduction with `r_i 0 = 0`, additive up to `H_i`, and
compatible with reduction modulo `p`. -/
theorem rep_spec (p : ℕ) [Fact p.Prime] {i : ℕ} (hi : 1 ≤ i) (g g' : ZMod (p ^ i)) :
    PadicInt.toZModPow i (rep p i g) = g ∧ rep p i 0 = 0 ∧
      rep p i g + rep p i g' - rep p i (g + g') ∈ padicSubgroup p i ∧
      ZMod.castHom (dvd_pow_self p (by omega)) (ZMod p) g = PadicInt.toZMod (rep p i g) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hq : ∀ h : ZMod (p ^ i), PadicInt.toZModPow i (rep p i h) = h := fun h => by
    simp [rep]
  refine ⟨hq g, by simp [rep], ?_, ?_⟩
  · rw [← ker_toZModPow_eq, AddMonoidHom.mem_ker]
    change PadicInt.toZModPow i (rep p i g + rep p i g' - rep p i (g + g')) = 0
    rw [map_sub, map_add, hq, hq, hq]
    abel
  · have : NeZero (p ^ i) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, rep, map_natCast]

end HSP
