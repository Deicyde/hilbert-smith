import Mathlib
import HilbertSmithPaper.ChainModels.Torus.Lift
import HilbertSmithPaper.ChainModels.Grid.Buffers.BufferedCells
import HilbertSmithPaper.ChainModels.Grid.Buffers.ControlLabels
import HilbertSmithPaper.ChainModels.Grid.Buffers.BasedInclusion
import HilbertSmithPaper.ChainModels.Grid.Buffers.Restriction
import HilbertSmithPaper.ChainModels.Grid.SphereLabels
import HilbertSmithPaper.Corner.Actions.GraphType
import HilbertSmithPaper.LocalData.Chart.OpenTestRegion
import HilbertSmithPaper.LocalData.Control.ControlActionIsometric
import HilbertSmithPaper.LocalData.Control.ControlMetricSpace
import HilbertSmithPaper.ChainModels.Grid.Buffers.BufferedSphereLabels
import HilbertSmithPaper.LocalData.Control.ControlIsometricAction
import HilbertSmithPaper.ChainModels.Grid.Model.ChainModelDualLabel
import HilbertSmithPaper.ChainModels.Grid.Model.ChainModelLabel
import HilbertSmithPaper.ChainModels.Grid.Buffers.SphereProp

/-!
# Buffered restriction

Five facts on buffered cells and restrictions `u^{[v,v']} = p_{v'} u ι_v`: buffered cells have
lifts in `U⁺`; small sphere propagation gives `u ι_v = ι_{v'} u^{[v,v']}`; graph types add under
composition, change sign under transposition and are preserved by sums; and small torus
propagation gives small sphere propagation and graph type `0`.

## Encoding

* The statements hold for any finite set of cells `B` with torus labels `x : B → 𝕋ⁿ` (for the
  cells of `D_i` and of `D_i^{N-*}`, `x` is `chainModelLabel` or `chainModelDualLabel`): the
  buffered cells `bufferedCells A ρ x v`, their control labels `controlLabel A hρ hρ' x v`, the
  based inclusion `ι_v = basedInc (bufferedCells A ρ x v)`, and the restriction `restrict`.
* Graph types are `Corner.IsGraphType` for the control labels, `T × Sⁿ` with the product metric
  and action (the action on `Sⁿ` is trivial). Sphere propagation is `sphereProp`, torus
  propagation `prop` for the torus labels.
-/

open CategoryTheory
open scoped NNReal

namespace HSP.ChainModels

open HSP.Corner

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

open Classical in
/-- **Buffered restriction.** For a local datum, `0 < ρ < ρ₊` and the torus test map `f_T` of
radius `ρ`:
1. a buffered cell has its lift `x̃_b` in `U⁺` (so `λ(b) = (π(x̃_b), s_b)`);
2. for `0 < v < v'` there is `η > 0` with `u ι_v = ι_{v'} u^{[v,v']}` whenever `u` has sphere
   propagation less than `η`;
3. for `0 < v < v'`, if `u ι_v = ι_{v'} u^{[v,v']}`, `u^{[v']}` has graph type `c` with bound `ε`
   and `u'^{[v']}` has graph type `c'` with bound `ε'`, then `(u'u)^{[v]}` has graph type
   `c + c'` with bound `ε + ε'`;
4. if `u^{[v]}` has graph type `c` with bound `ε`, then `(u^*)^{[v]}` has graph type `-c` with
   bound `ε`; if `u^{[v]}`, `u'^{[v]}` have graph type `c` with bound `ε`, so has `(u+u')^{[v]}`;
5. for every `ε > 0` there is `t > 0` such that every `u` with torus propagation at most `t` has
   sphere propagation at most `ε` and, for every `v > 0`, `u^{[v]}` has graph type `0` with
   bound `ε`. -/
theorem bufferedRestriction (A : LocalDatum p n D ρplus) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ' : ρ < ρplus) :
    -- (1)
    (∀ (v : ℝ) (y : Torus n), IsBufferedLabel v (torusTestMap A ρ y : Corner.RoundSphere n) →
      ∃ z ∈ A.Uplus, (z : EuclideanSpace ℝ (Fin n)) = Torus.lift y) ∧
    -- (2)
    (∀ v v' : ℝ, 0 < v → v < v' → ∃ η > 0, ∀ (B B' : Type) [Fintype B] [Fintype B']
      (x : B → Torus n) (x' : B' → Torus n) (u : Matrix B' B ℚ),
      (sphereProp A ρ x x' u : ℝ) < η →
        u * basedInc (bufferedCells A ρ x v) =
          basedInc (bufferedCells A ρ x' v') * restrict (bufferedCells A ρ x' v') (bufferedCells A ρ x v) u) ∧
    -- (3)
    (∀ v v' : ℝ, 0 < v → v < v' → ∀ (B B' B'' : Type) [Fintype B] [Fintype B'] [Fintype B'']
      (x : B → Torus n) (x' : B' → Torus n) (x'' : B'' → Torus n)
      (u : Matrix B' B ℚ) (u' : Matrix B'' B' ℚ) (c c' : ZMod p) (ε ε' : ℝ),
      u * basedInc (bufferedCells A ρ x v) =
          basedInc (bufferedCells A ρ x' v') * restrict (bufferedCells A ρ x' v') (bufferedCells A ρ x v) u →
      IsGraphType (controlLabel A hρ hρ' x v') (controlLabel A hρ hρ' x' v') c ε
        (restrict (bufferedCells A ρ x' v') (bufferedCells A ρ x v') u) →
      IsGraphType (controlLabel A hρ hρ' x' v') (controlLabel A hρ hρ' x'' v') c' ε'
        (restrict (bufferedCells A ρ x'' v') (bufferedCells A ρ x' v') u') →
      IsGraphType (controlLabel A hρ hρ' x v) (controlLabel A hρ hρ' x'' v) (c + c') (ε + ε')
        (restrict (bufferedCells A ρ x'' v) (bufferedCells A ρ x v) (u' * u))) ∧
    -- (4)
    (∀ (v : ℝ) (B B' : Type) (x : B → Torus n) (x' : B' → Torus n) (u u' : Matrix B' B ℚ)
      (c : ZMod p) (ε : ℝ),
      (IsGraphType (controlLabel A hρ hρ' x v) (controlLabel A hρ hρ' x' v) c ε
          (restrict (bufferedCells A ρ x' v) (bufferedCells A ρ x v) u) →
        IsGraphType (controlLabel A hρ hρ' x' v) (controlLabel A hρ hρ' x v) (-c) ε
          (restrict (bufferedCells A ρ x v) (bufferedCells A ρ x' v) u.transpose)) ∧
      (IsGraphType (controlLabel A hρ hρ' x v) (controlLabel A hρ hρ' x' v) c ε
          (restrict (bufferedCells A ρ x' v) (bufferedCells A ρ x v) u) →
        IsGraphType (controlLabel A hρ hρ' x v) (controlLabel A hρ hρ' x' v) c ε
          (restrict (bufferedCells A ρ x' v) (bufferedCells A ρ x v) u') →
        IsGraphType (controlLabel A hρ hρ' x v) (controlLabel A hρ hρ' x' v) c ε
          (restrict (bufferedCells A ρ x' v) (bufferedCells A ρ x v) (u + u')))) ∧
    -- (5)
    (∀ ε > 0, ∃ t > 0, ∀ (B B' : Type) [Fintype B] [Fintype B'] (x : B → Torus n)
      (x' : B' → Torus n) (u : Matrix B' B ℚ), (prop x x' u : ℝ) ≤ t →
        (sphereProp A ρ x x' u : ℝ) ≤ ε ∧
        ∀ v > 0, IsGraphType (controlLabel A hρ hρ' x v) (controlLabel A hρ hρ' x' v)
          (0 : ZMod p) ε (restrict (bufferedCells A ρ x' v) (bufferedCells A ρ x v) u)) := by
  sorry

end HSP.ChainModels
