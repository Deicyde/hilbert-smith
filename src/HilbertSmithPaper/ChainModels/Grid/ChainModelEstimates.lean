import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Buffers.BasedInclusion
import HilbertSmithPaper.ChainModels.Grid.Buffers.BufferedCells
import HilbertSmithPaper.ChainModels.Grid.Buffers.ControlLabels
import HilbertSmithPaper.ChainModels.Approximations.ChainModelFamily
import HilbertSmithPaper.ChainModels.Approximations.AdjointHomotopies
import HilbertSmithPaper.ChainModels.Approximations.ProductHomotopies
import HilbertSmithPaper.ChainModels.Approximations.IsometryHomotopies
import HilbertSmithPaper.ChainModels.Approximations.BufferedRestriction
import HilbertSmithPaper.ChainModels.Grid.Cubical.GridCube

/-!
# Chain-model estimates

The family `𝒫_i` of chain-model matrices satisfies, for a null sequence `(ε_i)`: small sphere
propagation, `a_0 = 1`, `a_g z_i = z_i`, `ε a_g = ε`, small sphere diameters of the cubes, graph
types of the restrictions `w^{[v]}` for large `i`, and buffer commutation for large `i`.

## Encoding

* `𝒫_i` is `chainModelFamily A hρ hρ' i` (the family of chain-model matrices), whose members
  are typed labelled matrices `w` with fields `w.x`, `w.x'`, `w.u`, `w.c`.
* Sphere propagation (`sphereProp`), restrictions (`restrict`, `bufferedCells`, `basedInc`),
  control labels (`controlLabel`) and graph types (`Corner.IsGraphType`) are those of the
  buffered restriction, for `f_T` of radius `0 < ρ < ρ₊`.
* `κ_i ≤ ε_i` is stated for every cube `c` of `C(k_i)`: `diam_S f_T(|c|) ≤ ε_i`.
-/

open CategoryTheory Filter Topology
open scoped NNReal

namespace HSP.ChainModels

open FreeQ DualCat HSP.Corner

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

open Classical in
/-- **Chain-model estimates.** There is a null sequence `(ε_i)` such that, for all `i` and
`g ∈ G_i`:
1. every `w ∈ 𝒫_i` has sphere propagation at most `ε_i`;
2. `a_0 = 1`, `a_g z_i = z_i` and `ε a_g = ε`;
3. `κ_i = max_c diam_S f_T(|c|) ≤ ε_i`, over the cubes `c` of `C(k_i)`;
4. for every `v > 0` there are `i₀` and a null sequence `(ε_i(v))` such that, for `i ≥ i₀` and
   every `w ∈ 𝒫_i`, `w^{[v]}` has graph type the type of `w`, with bound `ε_i(v)`;
5. for `0 < v < v'` there is `i₁` with `w ι_v = ι_{v'} w^{[v,v']}` for `i ≥ i₁`, `w ∈ 𝒫_i`. -/
theorem chainModel_estimates (A : LocalDatum p n D ρplus) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ' : ρ < ρplus) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      -- (1)
      (∀ i, ∀ w ∈ chainModelFamily A hρ hρ' i, (sphereProp A ρ w.x w.x' w.u : ℝ) ≤ ε i) ∧
      -- (2)
      (∀ (i : ℕ) (g : ZMod (p ^ i)),
        (∀ r, groupApprox A i 0 r = 𝟙 _) ∧
        chainModelFundamental A i ≫ groupApprox A i g ((n + 4 : ℕ) : ℤ) =
          chainModelFundamental A i ∧
        groupApprox A i g 0 ≫ chainModelAug A i = chainModelAug A i) ∧
      -- (3)
      (∀ (i : ℕ) (c : GridCube (meshSequence A i) n),
        Metric.diam ((fun y => (torusTestMap A ρ y : Corner.RoundSphere n)) '' c.realization) ≤
          ε i) ∧
      -- (4)
      (∀ v > 0, ∃ (i₀ : ℕ) (εv : ℕ → ℝ), Tendsto εv atTop (𝓝 0) ∧
        ∀ i ≥ i₀, ∀ w ∈ chainModelFamily A hρ hρ' i,
          IsGraphType (controlLabel A hρ hρ' w.x v) (controlLabel A hρ hρ' w.x' v) w.c (εv i)
            (restrict (bufferedCells A ρ w.x' v) (bufferedCells A ρ w.x v) w.u)) ∧
      -- (5)
      (∀ v v' : ℝ, 0 < v → v < v' → ∃ i₁ : ℕ, ∀ i ≥ i₁, ∀ w ∈ chainModelFamily A hρ hρ' i,
        w.u * basedInc (bufferedCells A ρ w.x v) =
          basedInc (bufferedCells A ρ w.x' v') *
            restrict (bufferedCells A ρ w.x' v') (bufferedCells A ρ w.x v) w.u) := by
  sorry

end HSP.ChainModels
