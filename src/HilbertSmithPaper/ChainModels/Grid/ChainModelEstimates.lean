import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Buffers.BasedInclusion
import HilbertSmithPaper.ChainModels.Grid.Buffers.BufferedCells
import HilbertSmithPaper.ChainModels.Grid.Buffers.ControlLabels
import HilbertSmithPaper.ChainModels.Approximations.ChosenIsometryHomotopies
import HilbertSmithPaper.ChainModels.Approximations.AdjointHomotopy
import HilbertSmithPaper.ChainModels.Approximations.ChosenProductHomotopies
import HilbertSmithPaper.ChainModels.Approximations.AdjointHomotopies
import HilbertSmithPaper.ChainModels.Approximations.ProductHomotopies
import HilbertSmithPaper.ChainModels.Approximations.IsometryHomotopies
import HilbertSmithPaper.ChainModels.Approximations.BufferedRestriction

/-!
# Chain-model estimates

The family `𝒫_i` of typed matrices (the differentials of `D_i` and `D_i^{N-*}`, `φ_i`, `b_i`,
`H_i`, `H'_i`, `U_g` of type `0`, `a_g` of type `χ_i(g)`, `a_g^*` of type `-χ_i(g)`, `B_{g,h}` of
type `χ_i(g+h)`, `V_g` of type `χ_i(g)`) satisfies, for a null sequence `(ε_i)`: small sphere
propagation, `a_0 = 1`, `a_g z_i = z_i`, `ε a_g = ε`, small sphere diameters of the cubes, graph
types of the restrictions `w^{[v]}` for large `i`, and buffer commutation for large `i`.

## Encoding

* A *typed labelled matrix* (`TypedMatrix n p`) is a matrix `u : ℚ^B → ℚ^{B'}` between finite
  sets of cells with torus labels `x`, `x'`, together with its type `c ∈ C_p`. The labels of a
  dual cell are those of the cell.
* `chainModelFamily A hρ hρ' i` is `𝒫_i`, with every map listed in each degree (each component
  for the elements `φ_i`, `U_g`, `V_g` of the structure complex), and the chosen
  `productHomotopy`, `isometryHomotopy`, `adjointHomotopy`.
* Sphere propagation (`sphereProp`), restrictions (`restrict`, `bufferedCells`, `basedInc`),
  control labels (`controlLabel`) and graph types (`Corner.IsGraphType`) are those of the
  buffered restriction, for `f_T` of radius `0 < ρ < ρ₊`; `χ_i = ZMod.cast`.
* `κ_i ≤ ε_i` is stated for every cube `c` of `C(k_i)`: `diam_S f_T(|c|) ≤ ε_i`.
-/

open CategoryTheory Filter Topology
open scoped NNReal

namespace HSP.ChainModels

open FreeQ DualCat HSP.Corner

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- A matrix `u : ℚ^B → ℚ^{B'}` between finite sets of cells with torus labels, with a type
`c ∈ C_p`. -/
structure TypedMatrix (n p : ℕ) where
  /-- The source cells. -/
  B : Type
  /-- The target cells. -/
  B' : Type
  [fintypeB : Fintype B]
  [fintypeB' : Fintype B']
  /-- The torus labels of the source cells. -/
  x : B → Torus n
  /-- The torus labels of the target cells. -/
  x' : B' → Torus n
  /-- The matrix. -/
  u : Matrix B' B ℚ
  /-- The type. -/
  c : ZMod p

attribute [instance] TypedMatrix.fintypeB TypedMatrix.fintypeB'

/-- The typed matrix `u` of type `c`, with source labels `x` and target labels `x'`. -/
def TypedMatrix.of {B B' : Type} [Fintype B] [Fintype B'] (x : B → Torus n) (x' : B' → Torus n)
    (u : Matrix B' B ℚ) (c : ZMod p) : TypedMatrix n p :=
  { B := B, B' := B', x := x, x' := x', u := u, c := c }

/-- The family `𝒫_i` of typed matrices of the chain model `D_i`, `N = n + 4`. -/
def chainModelFamily (A : LocalDatum p n D ρplus) {ρ : ℝ} (hρ : 0 < ρ) (hρ' : ρ < ρplus)
    (i : ℕ) : Set (TypedMatrix n p) :=
  let N : ℤ := ((n + 4 : ℕ) : ℤ)
  let l := chainModelLabel A i
  -- the differential of `D_i`
  {w | ∃ r : ℤ, w = .of (l r) (l (r - 1)) (toMatrix ((chainModel A i).d r (r - 1))) 0} ∪
  -- the differential of `D_i^{N-*}`
  {w | ∃ r : ℤ, w = .of (l (N - r)) (l (N - (r - 1)))
      (toMatrix ((dualCx (chainModel A i) N).d r (r - 1))) 0} ∪
  -- `φ_i`
  {w | ∃ y : {y : ℤ × ℤ // y.1 + y.2 = N}, w = .of (l y.1.2) (l y.1.1)
      (toMatrix ((chainModelDuality A i).φ y)) 0} ∪
  -- `b_i`
  {w | ∃ r : ℤ, w = .of (l r) (l (N - r)) (toMatrix ((chainModelDuality A i).b r)) 0} ∪
  -- `H_i`
  {w | ∃ r : ℤ, w = .of (l r) (l (r + 1)) (toMatrix (chainModelH A i r)) 0} ∪
  -- `H'_i`
  {w | ∃ r : ℤ, w = .of (l (N - r)) (l (N - (r + 1))) (toMatrix (chainModelH' A i r)) 0} ∪
  -- `U_g`
  {w | ∃ (g : ZMod (p ^ i)) (y : {y : ℤ × ℤ // y.1 + y.2 = N + 1}), w = .of (l y.1.2) (l y.1.1)
      (toMatrix (isometryHomotopy A i g y)) 0} ∪
  -- `a_g`
  {w | ∃ (g : ZMod (p ^ i)) (r : ℤ), w = .of (l r) (l r)
      (toMatrix (groupApprox A i g r)) (ZMod.cast g)} ∪
  -- `a_g^*`
  {w | ∃ (g : ZMod (p ^ i)) (r : ℤ), w = .of (l r) (l r)
      (toMatrix (dualHom (groupApprox A i g r))) (-ZMod.cast g)} ∪
  -- `B_{g,h}`
  {w | ∃ (g h : ZMod (p ^ i)) (r : ℤ), w = .of (l r) (l (r + 1))
      (toMatrix (productHomotopy A hρ hρ' i g h r)) (ZMod.cast (g + h))} ∪
  -- `V_g`
  {w | ∃ (g : ZMod (p ^ i)) (y : {y : ℤ × ℤ // y.1 + y.2 = N + 1}), w = .of (l y.1.2) (l y.1.1)
      (toMatrix (adjointHomotopy A hρ hρ' i g y)) (ZMod.cast g)}

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
