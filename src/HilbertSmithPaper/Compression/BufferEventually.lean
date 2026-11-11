import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Buffers.BasedInclusion
import HilbertSmithPaper.ChainModels.Grid.Buffers.BufferedCells
import HilbertSmithPaper.ChainModels.Grid.Buffers.ControlLabels
import HilbertSmithPaper.Compression.RetainedCells
import HilbertSmithPaper.ChainModels.Grid.ChainModelEstimates

/-!
# Buffers hold eventually

For fixed local data with buffer radii `t < u` and `t' = (t + u)/2`, and the family `𝒫_i` of the
chain-model estimates, there are `i₁` and a null sequence `(ε'_i)` such that for every `i ≥ i₁`:
retained cells and their duals lie in `𝓑_i(t')`; every `w ∈ 𝒫_i` has `w ι_{t'} = ι_u w^{[t',u]}`;
and every `w^{[u]}` has graph type the type of `w`, with bound `ε'_i`, for the control labels.

## Encoding

* The test map, sphere labels and control labels use the pinch radius `ρ` of the fixed local data
  (`F.ρ_pos`, `F.ρ_lt`).
* `BuffersHold F ε' i` is the conjunction of items (1)-(3) at the index `i` with the bound
  `ε'_i`; the lemma `buffer_eventually` asserts a null sequence `ε'` with `BuffersHold F ε' i`
  for all large `i` (`∀ᶠ i in atTop`, which is "there is `i₁` such that for every `i ≥ i₁`").
* The dual of a cell of `(D_i)_{N-r}` is a cell of `(D_i^{N-*})_r` with the same index
  (`IsRetainedDual`, and `bufferedCells` with `chainModelDualLabel`).
-/

open CategoryTheory Filter Topology

namespace HSP.Compression

open HSP.ChainModels HSP.Corner

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

open Classical in
/-- Items (1)-(3) of "buffers hold eventually" at the index `i`, with the bound `ε'_i`,
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

/-- **Buffers hold eventually.** There are an index `i₁` and a null sequence `(ε'_i)` such that,
for every `i ≥ i₁`: every retained cell of `D_i`, and its dual, lies in `𝓑_i(t')`; every
`w ∈ 𝒫_i` satisfies `w ι_{t'} = ι_u w^{[t',u]}`; and every `w^{[u]}` has graph type the type of
`w`, with bound `ε'_i`, for the control labels. -/
theorem buffer_eventually (F : FixedLocalData p n D ρplus) :
    ∃ ε' : ℕ → ℝ, Tendsto ε' atTop (𝓝 0) ∧ ∀ᶠ i in atTop, BuffersHold F ε' i := by
  sorry

end HSP.Compression
