import Mathlib
import HilbertSmithPaper.ChainModels.Approximations.IsometryHomotopies
import HilbertSmithPaper.ChainModels.Approximations.ProductHomotopies

/-!
# Adjoint homotopies

For `g ∈ G_i`, `a = a_g`, `a' = a_{-g}` and `S = B_{-g,g}` (so `a'a - 1 = dS + Sd`), let `K` be the
map of degree `+1` of `D_i^{N-*}` given by `(-1)^r S^*` in degree `r`, and
`V_g = aφ_iK + U_g a'^*`. Then `dV_g + V_g d = a_gφ_i - φ_i a_{-g}^*`, and there is a null
sequence `(μ''_i)` with `V_g` of sphere propagation at most `μ''_i` and, for every `v > 0`,
`V_g^{[v]}` of graph type `χ_i(g)` with bound `μ''_i` for all large `i`.

## Encoding

* `V_g` is a map of degree `+1` from `D_i^{N-*}` to `D_i`, i.e. an element of `M(D_i)_{N+1}`
  (`adjointHomotopy`): its component from `(D_i^{N-*})_{N-q} = (D_i)_q^*` to `(D_i)_p`,
  `p + q = N + 1`, is `(-1)^{N-q} (S_{q-1})^* ≫ φ_i ≫ (a_g)_p + (a_{-g})_q^* ≫ U_g`.
* `S` and `U_g` are the chosen `productHomotopy` and `isometryHomotopy`; `dV + Vd` is the
  differential of `M(D_i)` (`StructureCx.d_apply`), as for `U_g`.
* Sphere propagation, restriction, graph types and `χ_i` are as in product homotopies; cells
  and duals carry the same labels.
-/

open CategoryTheory Filter Topology
open scoped NNReal

namespace HSP.ChainModels

open FreeQ DualCat HSP.Corner

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The *adjoint homotopy* `V_g = a_g φ_i K + U_g a_{-g}^* ∈ M(D_i)_{N+1}`, `K = (-1)^r S^*` in
degree `r` of `D_i^{N-*}`, `S = B_{-g,g}`. -/
noncomputable def adjointHomotopy (A : LocalDatum p n D ρplus) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ' : ρ < ρplus) (i : ℕ) (g : ZMod (p ^ i)) :
    (StructureCx (chainModel A i)).X (((n + 4 : ℕ) : ℤ) + 1) := fun x =>
  (((n + 4 : ℕ) : ℤ) - x.1.2).negOnePow •
      (eqToHom (congrArg (fun t => dual ((chainModel A i).X t))
          (show x.1.2 = x.1.2 - 1 + 1 by ring)) ≫
        dualHom (productHomotopy A hρ hρ' i (-g) g (x.1.2 - 1)) ≫
        (chainModelDuality A i).φ
          ⟨(x.1.1, x.1.2 - 1), by have := x.2; push_cast at this ⊢; omega⟩ ≫
        groupApprox A i g x.1.1) +
    dualHom (groupApprox A i (-g) x.1.2) ≫ isometryHomotopy A i g x

/-- **Adjoint homotopies.** For `g ∈ G_i`:
1. `dV_g + V_g d = a_g φ_i - φ_i a_{-g}^*`;
2. there is a null sequence `(μ''_i)` such that `V_g` has sphere propagation at most `μ''_i`
   and, for every `v > 0`, `V_g^{[v]}` has graph type `χ_i(g)` with bound `μ''_i` for all large
   `i`. -/
theorem adjoint_homotopies (A : LocalDatum p n D ρplus) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ' : ρ < ρplus) :
    -- (1)
    (∀ (i : ℕ) (g : ZMod (p ^ i)) (x : {x : ℤ × ℤ // x.1 + x.2 = ((n + 4 : ℕ) : ℤ)}),
      (StructureCx (chainModel A i)).d (((n + 4 : ℕ) : ℤ) + 1) ((n + 4 : ℕ) : ℤ)
          (adjointHomotopy A hρ hρ' i g) x =
        (chainModelDuality A i).φ x ≫ groupApprox A i g x.1.1 -
          dualHom (groupApprox A i (-g) x.1.2) ≫ (chainModelDuality A i).φ x) ∧
    -- (2)
    ∃ μ'' : ℕ → ℝ, Tendsto μ'' atTop (𝓝 0) ∧
      (∀ (i : ℕ) (g : ZMod (p ^ i)) (x : {x : ℤ × ℤ // x.1 + x.2 = ((n + 4 : ℕ) : ℤ) + 1}),
        (sphereProp A ρ (chainModelLabel A i x.1.2) (chainModelLabel A i x.1.1)
          (adjointHomotopy A hρ hρ' i g x) : ℝ) ≤ μ'' i) ∧
      ∀ v > 0, ∀ᶠ i in atTop, ∀ (g : ZMod (p ^ i))
        (x : {x : ℤ × ℤ // x.1 + x.2 = ((n + 4 : ℕ) : ℤ) + 1}),
        IsGraphType (bufferedLabel A hρ hρ' (chainModelLabel A i x.1.2) v)
          (bufferedLabel A hρ hρ' (chainModelLabel A i x.1.1) v) (ZMod.cast g : ZMod p) (μ'' i)
          (restrict (bufferedSet A ρ (chainModelLabel A i x.1.1) v)
            (bufferedSet A ρ (chainModelLabel A i x.1.2) v) (adjointHomotopy A hρ hρ' i g x)) := by
  sorry

end HSP.ChainModels
