import Mathlib
import HilbertSmithPaper.ChainModels.Approximations.ProductHomotopies
import HilbertSmithPaper.ChainModels.Grid.Model.ChainModelLabel
import HilbertSmithPaper.ChainModels.Grid.Buffers.SphereProp

/-!
# Chosen product homotopies

Fix a family `B^T_{g,h}` given by product homotopies for the radius `ρ`, and put
`B_{g,h} = B^T_{g,h} ⊗ 1_P`.

## Encoding

`productHomotopy A hρ hρ' i g h r` (the declaration of the article) is the degree-`r` component of
`B_{g,h}`, `tensorOneP` of degree `1` of the family chosen (`Exists.choose`) from
`product_homotopies`; `productHomotopy_spec` records its properties.
-/

open CategoryTheory Filter Topology

namespace HSP.ChainModels

open FreeQ HSP.Corner

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The chosen product homotopy `B_{g,h} = B^T_{g,h} ⊗ 1_P` in degree `r`. -/
noncomputable def productHomotopy (A : LocalDatum p n D ρplus) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ' : ρ < ρplus) (i : ℕ) (g h : ZMod (p ^ i)) (r : ℤ) :
    (chainModel A i).X r ⟶ (chainModel A i).X (r + 1) :=
  tensorOneP A i 1 ((product_homotopies A hρ hρ').choose i g h) r

/-- The properties of the chosen product homotopies. -/
lemma productHomotopy_spec (A : LocalDatum p n D ρplus) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ' : ρ < ρplus) :
    ∃ μ' : ℕ → ℝ, Tendsto μ' atTop (𝓝 0) ∧
      ∀ (i : ℕ) (g h : ZMod (p ^ i)),
        (∀ r : ℤ, groupApprox A i h r ≫ groupApprox A i g r - groupApprox A i (g + h) r =
          productHomotopy A hρ hρ' i g h r ≫ (chainModel A i).d (r + 1) r +
            (chainModel A i).d r (r - 1) ≫ productHomotopy A hρ hρ' i g h (r - 1) ≫
              eqToHom (congrArg (chainModel A i).X (by ring))) ∧
        (∀ r : ℤ, (sphereProp A ρ (chainModelLabel A i r) (chainModelLabel A i (r + 1))
          (toMatrix (productHomotopy A hρ hρ' i g h r)) : ℝ) ≤ μ' i) ∧
        (∀ v > 0, ∀ r : ℤ,
          IsGraphType (controlLabel A hρ hρ' (chainModelLabel A i r) v)
            (controlLabel A hρ hρ' (chainModelLabel A i (r + 1)) v)
            (ZMod.cast (g + h) : ZMod p) (μ' i)
            (restrict (bufferedCells A ρ (chainModelLabel A i (r + 1)) v)
              (bufferedCells A ρ (chainModelLabel A i r) v)
              (toMatrix (productHomotopy A hρ hρ' i g h r)))) :=
  (product_homotopies A hρ hρ').choose_spec

end HSP.ChainModels
