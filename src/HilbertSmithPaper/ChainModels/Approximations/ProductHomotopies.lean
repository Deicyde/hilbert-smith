import Mathlib
import HilbertSmithPaper.ChainModels.Approximations.GroupApprox
import HilbertSmithPaper.ChainModels.Grid.Tensor.TensorOneP
import HilbertSmithPaper.ChainModels.Approximations.BufferedRestriction

/-!
# Product homotopies

For `g, h ∈ G_i` there are `B_{g,h} = B^T_{g,h} ⊗ 1_P` of degree `+1` with
`a_g a_h - a_{g+h} = dB_{g,h} + B_{g,h}d`, and a null sequence `(μ'_i)`, such that every `B_{g,h}`
has sphere propagation at most `μ'_i` and, for every `v > 0`, `B_{g,h}^{[v]}` has graph type
`χ_i(g+h)` with bound `μ'_i` for the control labels.

## Encoding

* `G_i = ℤ/p^i` (the representatives' groups), and `χ_i : G_i → C_p` is reduction mod `p`,
  `ZMod.cast`.
* A map of degree `+1` of `C(k_i)` is a family `(C(k_i))_r → (C(k_i))_{r+1}`; `tensorOneP A i 1 f`
  is `f ⊗ 1_P` on `D_i` (`basedTensorHom` with the identity of `P`).
* `a_g a_h` is `a_h ≫ a_g` in each degree; the homotopy identity is written in each degree `r`
  as `a_h a_g - a_{g+h} = B_r ≫ d + d ≫ B_{r-1}`.
* Sphere labels and control labels come from `f_T` of radius `ρ`, `0 < ρ < ρ₊`; sphere
  propagation is `sphereProp`, the restriction `B^{[v]}` is `restrict` to the buffered cells, and
  graph types are `Corner.IsGraphType` for `bufferedLabel`.
* `productHomotopyT A hρ hρ'` is a chosen family `B^T`.
-/

open CategoryTheory Filter Topology
open scoped NNReal

namespace HSP.ChainModels

open FreeQ HSP.Corner

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- **Product homotopies.** There are `B_{g,h} = B^T_{g,h} ⊗ 1_P` of degree `+1` with
`a_g a_h - a_{g+h} = dB_{g,h} + B_{g,h}d`, and a null sequence `(μ'_i)`, such that every `B_{g,h}`
has sphere propagation at most `μ'_i` and, for every `v > 0`, `B_{g,h}^{[v]}` has graph type
`χ_i(g+h)` with bound `μ'_i` for the control labels. -/
theorem product_homotopies (A : LocalDatum p n D ρplus) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ' : ρ < ρplus) :
    ∃ (BT : ∀ (i : ℕ) (_ _ : ZMod (p ^ i)) (r : ℤ),
        (gridComplex (meshSequence A i) n).X r ⟶ (gridComplex (meshSequence A i) n).X (r + 1))
      (μ' : ℕ → ℝ), Tendsto μ' atTop (𝓝 0) ∧
      ∀ (i : ℕ) (g h : ZMod (p ^ i)),
        (∀ r : ℤ, groupApprox A i h r ≫ groupApprox A i g r - groupApprox A i (g + h) r =
          tensorOneP A i 1 (BT i g h) r ≫ (chainModel A i).d (r + 1) r +
            (chainModel A i).d r (r - 1) ≫ tensorOneP A i 1 (BT i g h) (r - 1) ≫
              eqToHom (congrArg (chainModel A i).X (by ring))) ∧
        (∀ r : ℤ, (sphereProp A ρ (chainModelLabel A i r) (chainModelLabel A i (r + 1))
          (toMatrix (tensorOneP A i 1 (BT i g h) r)) : ℝ) ≤ μ' i) ∧
        (∀ v > 0, ∀ r : ℤ,
          IsGraphType (bufferedLabel A hρ hρ' (chainModelLabel A i r) v)
            (bufferedLabel A hρ hρ' (chainModelLabel A i (r + 1)) v)
            (ZMod.cast (g + h) : ZMod p) (μ' i)
            (restrict (bufferedSet A ρ (chainModelLabel A i (r + 1)) v)
              (bufferedSet A ρ (chainModelLabel A i r) v)
              (toMatrix (tensorOneP A i 1 (BT i g h) r)))) := by
  sorry

/-- A chosen family `B^T_{g,h}` of the product homotopies. -/
noncomputable def productHomotopyT (A : LocalDatum p n D ρplus) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ' : ρ < ρplus) (i : ℕ) (g h : ZMod (p ^ i)) (r : ℤ) :
    (gridComplex (meshSequence A i) n).X r ⟶ (gridComplex (meshSequence A i) n).X (r + 1) :=
  (product_homotopies A hρ hρ').choose i g h r

/-- The product homotopy `B_{g,h} = B^T_{g,h} ⊗ 1_P` in degree `r`. -/
noncomputable def productHomotopy (A : LocalDatum p n D ρplus) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ' : ρ < ρplus) (i : ℕ) (g h : ZMod (p ^ i)) (r : ℤ) :
    (chainModel A i).X r ⟶ (chainModel A i).X (r + 1) :=
  tensorOneP A i 1 (productHomotopyT A hρ hρ' i g h) r

end HSP.ChainModels
