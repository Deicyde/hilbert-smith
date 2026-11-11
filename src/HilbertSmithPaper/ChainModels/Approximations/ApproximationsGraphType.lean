import Mathlib
import HilbertSmithPaper.ChainModels.Approximations.GroupApprox
import HilbertSmithPaper.ChainModels.Approximations.BufferedRestriction
import HilbertSmithPaper.ChainModels.Grid.Model.ChainModelLabel
import HilbertSmithPaper.ChainModels.Grid.Buffers.SphereProp

/-!
# Graph type of approximations

There is a null sequence `(μ_i)` such that, for all `i`, `g ∈ G_i` and `v > 0`, `a_g` has sphere
propagation at most `μ_i` and `a_g^{[v]}` has graph type `χ_i(g)` with bound `μ_i` for the control
labels.

## Encoding

As in product homotopies: labels from `f_T` of radius `0 < ρ < ρ₊`, `sphereProp`, the square
restriction to buffered cells (`restrict`, `bufferedCells`), `Corner.IsGraphType` for
`controlLabel`, and `χ_i = ZMod.cast`. The statement is made in every degree `r`.
-/

open CategoryTheory Filter Topology
open scoped NNReal

namespace HSP.ChainModels

open FreeQ HSP.Corner

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- **Graph type of approximations.** There is a null sequence `(μ_i)` such that, for all `i`,
`g ∈ G_i` and `v > 0`, `a_g` has sphere propagation at most `μ_i` and `a_g^{[v]}` has graph type
`χ_i(g)` with bound `μ_i`. -/
theorem approx_graphType (A : LocalDatum p n D ρplus) {ρ : ℝ} (hρ : 0 < ρ) (hρ' : ρ < ρplus) :
    ∃ μ : ℕ → ℝ, Tendsto μ atTop (𝓝 0) ∧
      ∀ (i : ℕ) (g : ZMod (p ^ i)) (r : ℤ),
        (sphereProp A ρ (chainModelLabel A i r) (chainModelLabel A i r)
          (toMatrix (groupApprox A i g r)) : ℝ) ≤ μ i ∧
        ∀ v > 0, IsGraphType (controlLabel A hρ hρ' (chainModelLabel A i r) v)
          (controlLabel A hρ hρ' (chainModelLabel A i r) v) (ZMod.cast g : ZMod p) (μ i)
          (restrict (bufferedCells A ρ (chainModelLabel A i r) v)
            (bufferedCells A ρ (chainModelLabel A i r) v) (toMatrix (groupApprox A i g r))) := by
  sorry

end HSP.ChainModels
