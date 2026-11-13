import Mathlib
import HilbertSmithPaper.ChainModels.Grid.ChainModelPoincare
import HilbertSmithPaper.ChainModels.Approximations.ChosenIsometryHomotopies
import HilbertSmithPaper.ChainModels.Approximations.ChosenProductHomotopies
import HilbertSmithPaper.ChainModels.Approximations.AdjointHomotopy
import HilbertSmithPaper.ChainModels.Grid.Model.ChainModelLabel
import HilbertSmithPaper.ChainModels.Approximations.TypedMatrix

/-!
# The family of chain-model matrices

The family `𝒫_i` of typed labelled matrices of the chain model `D_i`: the differentials of `D_i`
and `D_i^{N-*}`, `φ_i`, `b_i`, `H_i`, `H'_i`, `U_g` of type `0`, `a_g` of type `χ_i(g)`, `a_g^*`
of type `-χ_i(g)`, `B_{g,h}` of type `χ_i(g+h)` and `V_g` of type `χ_i(g)`, for `g, h ∈ G_i`.

## Encoding

* Typed labelled matrices (`TypedMatrix n p`) are in `ChainModels.Approximations.TypedMatrix`.
  The labels of a dual cell are those of the cell.
* `chainModelFamily A hρ hρ' i` (the declaration of the article) is `𝒫_i`, with every map listed
  in each degree (each component for the elements `φ_i`, `U_g`, `V_g` of the structure complex),
  and the chosen `productHomotopy`, `isometryHomotopy`, `adjointHomotopy`; `χ_i = ZMod.cast`.
  The radius `0 < ρ < ρ₊` enters through the chosen product homotopies.
-/

open CategoryTheory

namespace HSP.ChainModels

open FreeQ DualCat

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

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

end HSP.ChainModels
