import Mathlib
import HilbertSmithPaper.ChainModels.Approximations.ChainApprox
import HilbertSmithPaper.ChainModels.Approximations.CompletedMap
import HilbertSmithPaper.ChainModels.Grid.ChainModel
import HilbertSmithPaper.ChainModels.Approximations.TensorOneP

/-!
# Group approximations

For `g ∈ G_i = ℤ/p^i`, `a_g = a_{g,i} = 1` if `g = 0`, and `a_{g,i} = a_i[\widehat{r_i(g)}] ⊗ 1_P`
otherwise, with the chain approximation `a_i[L]` and the completed representative
`\widehat{r_i(g)}`.

## Encoding

`groupApprox A i g r` (the declaration of the article) is the degree-`r` component
`(D_i)_r → (D_i)_r` of `a_{g,i}`: the identity for `g = 0`, and otherwise `a_i[\widehat{r_i(g)}] ⊗ 1_P`
(`tensorOneP` in degree `0`, with the identifications `r + 0 = r`).
-/

open CategoryTheory

namespace HSP.ChainModels

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The *group approximation* `a_{g,i}` in degree `r`: the identity if `g = 0`, and
`a_i[\widehat{r_i(g)}] ⊗ 1_P` otherwise. -/
noncomputable def groupApprox (A : LocalDatum p n D ρplus) (i : ℕ) (g : ZMod (p ^ i)) (r : ℤ) :
    (chainModel A i).X r ⟶ (chainModel A i).X r :=
  if g = 0 then 𝟙 _ else
    tensorOneP A i 0 (fun s => (chainApprox A i (completedMap_mem_trackFamily A (rep p i g))).f s ≫
        eqToHom (congrArg (gridComplex (meshSequence A i) n).X (add_zero s).symm)) r ≫
      eqToHom (congrArg (chainModel A i).X (add_zero r))

end HSP.ChainModels
