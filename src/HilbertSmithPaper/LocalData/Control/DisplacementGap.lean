import Mathlib
import HilbertSmithPaper.LocalData.Control.ControlActionFree
import HilbertSmithPaper.LocalData.Control.ControlActionIsometric
import HilbertSmithPaper.LocalData.Control.ControlSpaceCompact

/-!
# A uniform displacement gap

There is `ε > 0` with `ε ≤ d_T t (c +ᵥ t)` for all `t ∈ T` and `c ≠ 0` in `C_p`. For each `c ≠ 0`,
`t ↦ d_T t (c +ᵥ t)` is continuous (the action is isometric) and positive (the action is free), so
it has a positive minimum on the compact `T` (any positive bound works if `T` is empty); take the
least of these finitely many bounds.
-/

namespace HSP

/-- Distinct translates of a point of the control space stay a uniform distance apart. -/
theorem LocalDatum.exists_displacement_gap {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}
    (A : LocalDatum p n D ρplus) :
    ∃ ε > 0, ∀ t : A.T, ∀ c : ZMod p, c ≠ 0 → ε ≤ A.dT t (c +ᵥ t) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  have hc : ∀ c : ZMod p, c ≠ 0 → ∃ ε > 0, ∀ t : A.T, ε ≤ A.dT t (c +ᵥ t) := by
    intro c hc
    rcases isEmpty_or_nonempty A.T with hT | hT
    · exact ⟨1, one_pos, fun t => (IsEmpty.false t).elim⟩
    · have hcont : Continuous fun t : A.T => dist t (c +ᵥ t) :=
        continuous_id.dist (continuous_const_vadd c)
      obtain ⟨t₀, -, ht₀⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hcont.continuousOn
      refine ⟨dist t₀ (c +ᵥ t₀), ?_, fun t => ht₀ (Set.mem_univ t)⟩
      exact dist_pos.2 fun h => hc (A.free c t₀ h.symm)
  choose! ε hε hεt using hc
  set S := (Finset.univ : Finset (ZMod p)).filter (· ≠ 0) with hSdef
  have hS : S.Nonempty := ⟨1, by simp [S]⟩
  refine ⟨S.inf' hS ε, (Finset.lt_inf'_iff hS).2 fun c hc => hε c (Finset.mem_filter.1 hc).2,
    fun t c hc => ?_⟩
  exact (Finset.inf'_le _ (by simp [S, hc])).trans (hεt c hc t)

end HSP
