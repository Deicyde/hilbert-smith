import Mathlib
import HilbertSmithPaper.LocalData.Chart.LocalDatum
import HilbertSmithPaper.LocalData.Control.RepresentativeMap

/-!
# The track defect

For a local datum and `i ≥ 0`, `β_i = trackDefect A i` is the supremum over `g, h ∈ ℤ/p^i` and
`x ∈ Ω` with `|x| ≤ 3/8` of `|r_i(g)·(r_i(h)·x) - r_i(g+h)·x|`; the points are taken in `ℝⁿ`.
As a real `sSup`, it is `0` if this set is empty or unbounded.
-/

namespace HSP.ChainModels

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- `β_i = sup {|r_i(g)·(r_i(h)·x) - r_i(g+h)·x| : g, h ∈ ℤ/p^i, |x| ≤ 3/8}`. -/
noncomputable def trackDefect (A : LocalDatum p n D ρplus) (i : ℕ) : ℝ :=
  sSup {δ | ∃ g h : ZMod (p ^ i), ∃ x : A.Ω, ‖(x : EuclideanSpace ℝ (Fin n))‖ ≤ 3 / 8 ∧
    δ = dist ((rep p i g +ᵥ (rep p i h +ᵥ x) : A.Ω) : EuclideanSpace ℝ (Fin n))
      ((rep p i (g + h) +ᵥ x : A.Ω) : EuclideanSpace ℝ (Fin n))}

end HSP.ChainModels
