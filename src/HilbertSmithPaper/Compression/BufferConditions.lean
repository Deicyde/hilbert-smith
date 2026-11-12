import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Buffers.BasedInclusion
import HilbertSmithPaper.ChainModels.Grid.Buffers.BufferedCells
import HilbertSmithPaper.ChainModels.Grid.Buffers.ControlLabels
import HilbertSmithPaper.ChainModels.Grid.Buffers.Restriction
import HilbertSmithPaper.Corner.Actions.GraphType
import HilbertSmithPaper.Compression.RetainedCells
import HilbertSmithPaper.ChainModels.Approximations.ChainModelFamily
import HilbertSmithPaper.ChainModels.Grid.Model.ChainModelDualLabel
import HilbertSmithPaper.ChainModels.Grid.Model.ChainModelLabel

/-!
# Buffer conditions

For fixed local data with buffer radii `t < u`, `t' = (t + u)/2`, the family `𝒫_i` of
chain-model matrices for the radius `ρ`, and a bound `ε'_i`, the buffer conditions at `i` are:
retained cells and their duals lie in `𝓑_i(t')`; every `w ∈ 𝒫_i` has `w ι_{t'} = ι_u w^{[t',u]}`;
and every `w^{[u]}` has graph type the type of `w`, with bound `ε'_i`, for the control labels.

## Encoding

* The test map, sphere labels and control labels use the pinch radius `ρ` of the fixed local data
  (`F.ρ_pos`, `F.ρ_lt`).
* `BuffersHold F ε' i` (the declaration of the article) is the conjunction of conditions (1)-(3)
  at the index `i` with the bound `ε'_i`.
* The dual of a cell of `(D_i)_{N-r}` is a cell of `(D_i^{N-*})_r` with the same index
  (`IsRetainedDual`, and `bufferedCells` with `chainModelDualLabel`).
-/

namespace HSP.Compression

open HSP.ChainModels HSP.Corner

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

open Classical in
/-- The buffer conditions (1)-(3) at the index `i`, with the bound `ε'_i`,
`t' = (t + u)/2`. -/
def BuffersHold (F : FixedLocalData p n D ρplus) (ε' : ℕ → ℝ) (i : ℕ) : Prop :=
  -- (1)
  ((∀ (r : ℤ) (a : Fin ((chainModel F.toLocalDatum i).X r).dim), IsRetained F i r a →
      a ∈ bufferedCells F.toLocalDatum F.ρ (chainModelLabel F.toLocalDatum i r)
        ((F.t + F.u) / 2)) ∧
    ∀ (r : ℤ) (a : Fin ((chainModel F.toLocalDatum i).X ((n + 4 : ℕ) - r)).dim),
      IsRetainedDual F i r a →
        a ∈ bufferedCells F.toLocalDatum F.ρ (chainModelDualLabel F.toLocalDatum i r)
          ((F.t + F.u) / 2)) ∧
  -- (2)
  (∀ w ∈ chainModelFamily F.toLocalDatum F.ρ_pos F.ρ_lt i,
    w.u * basedInc (bufferedCells F.toLocalDatum F.ρ w.x ((F.t + F.u) / 2)) =
      basedInc (bufferedCells F.toLocalDatum F.ρ w.x' F.u) *
        restrict (bufferedCells F.toLocalDatum F.ρ w.x' F.u)
          (bufferedCells F.toLocalDatum F.ρ w.x ((F.t + F.u) / 2)) w.u) ∧
  -- (3)
  (∀ w ∈ chainModelFamily F.toLocalDatum F.ρ_pos F.ρ_lt i,
    IsGraphType (controlLabel F.toLocalDatum F.ρ_pos F.ρ_lt w.x F.u)
      (controlLabel F.toLocalDatum F.ρ_pos F.ρ_lt w.x' F.u) w.c (ε' i)
      (restrict (bufferedCells F.toLocalDatum F.ρ w.x' F.u)
        (bufferedCells F.toLocalDatum F.ρ w.x F.u) w.u))


end HSP.Compression
