import Mathlib
import HilbertSmithPaper.Corner.StandingData
import HilbertSmithPaper.LocalData.Control.FixedLocalData
import HilbertSmithPaper.LocalData.Control.ControlSpaceCompact
import HilbertSmithPaper.LocalData.Control.ControlActionFree
import HilbertSmithPaper.LocalData.Control.ControlActionIsometric
import HilbertSmithPaper.LocalData.Control.ControlMetricSpace
import HilbertSmithPaper.LocalData.Control.ControlIsometricAction

/-!
# Standing data of the compression

Take fixed local data with buffer radius `R` and nonempty control space `T`, and `0 < s < R / √n`.
Then `p`, the group sequence `G_i = ℤ/p^{max(i,1)}` with `χ_i` reduction mod `p`, `T` with the
orbit metric and the cyclic action, `n`, `R` and `s` form standing data.

## Encoding

* `standingData F hs hs'` (the declaration of the article) is the `Corner.StandingData` with
  exponents `a_i = max i 1` and `χ_i = ZMod.castHom` (reduction mod `p`, which is onto); `T` is
  the control space with its metric and cyclic action (compact, free and isometric by the
  control-space lemmas), nonempty by the instance argument.
* `n ≥ 1` holds for every local datum: in dimension `0` the domain is a point, and the
  no-fixed-point axiom moves the origin.
-/

namespace HSP.Compression

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- A local datum lives in dimension `n ≥ 1`. -/
private theorem one_le_n (F : FixedLocalData p n D ρplus) : 1 ≤ n := by
  by_contra h
  obtain rfl : n = 0 := by omega
  have h0 : (0 : EuclideanSpace ℝ (Fin 0)) ∈ F.Ω := F.ball_subset (Metric.mem_ball_self two_pos)
  obtain ⟨a, ha⟩ := F.exists_moved ⟨0, h0⟩ (by simpa using F.ρplus_pos.le)
  exact ha (Subtype.ext (Subsingleton.elim _ _))

/-- The *standing data of the compression*: `p`, `G_i = ℤ/p^{max(i,1)}` with reduction mod `p`,
the control space `T` with its orbit metric and cyclic action, `n`, `R` and `s`. -/
noncomputable def standingData (F : FixedLocalData p n D ρplus) [Nonempty F.T] {s : ℝ}
    (hs : 0 < s) (hs' : s < F.R / √n) : Corner.StandingData where
  p := p
  a i := max i 1
  one_le_a i := le_max_right i 1
  χ i := (ZMod.castHom (dvd_pow_self p (by omega : max i 1 ≠ 0)) (ZMod p)).toAddMonoidHom
  χ_surjective _ := ZMod.ringHom_surjective _
  T := F.T
  free := F.free
  n := n
  one_le_n := one_le_n F
  R := F.R
  s := s
  R_pos := F.r_pos.trans F.r_lt_R
  s_pos := hs
  s_lt := hs'

end HSP.Compression
