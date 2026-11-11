import Mathlib
import HilbertSmithPaper.ChainModels.Approximations.ChainApprox
import HilbertSmithPaper.ChainModels.Approximations.CompletedMap
import HilbertSmithPaper.ChainModels.Grid.ChainModel
import HilbertSmithPaper.ChainModels.Grid.ChainModelPoincare

/-!
# Group approximations

For `g ∈ G_i = ℤ/p^i`, `a_g = a_{g,i} = 1` if `g = 0`, and `a_{g,i} = a_i[\widehat{r_i(g)}] ⊗ 1_P`
otherwise, with the chain approximation `a_i[L]` and the completed representative
`\widehat{r_i(g)}`.

## Encoding

`groupApprox A i g r` (the declaration of the article) is the degree-`r` component
`(D_i)_r → (D_i)_r` of `a_{g,i}`: the identity for `g = 0`, and otherwise the tensor (`chainTensorOneP`)
`a_i[\widehat{r_i(g)}] ⊗ 1_P` of maps of degree `0` in the explicit bases of `D_i = C(k_i) ⊗ P`
(`basedTensorHom`, with the identity `idDeg0` of `P`).
-/

open CategoryTheory

namespace HSP.ChainModels

open FreeQ

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

private lemma cp2Complex_dim_neg_ga : ∀ q < 0, (cp2Complex.X q).dim = 0 := by
  intro q hq
  rcases q with q | q
  · exact absurd hq (by simp)
  · rfl

/-- The map `a ⊗ 1_P` of `D_i = C(k_i) ⊗ P` in degree `r`, for a chain map `a` of `C(k_i)`. -/
noncomputable def chainTensorOneP (A : LocalDatum p n D ρplus) (i : ℕ)
    (a : gridComplex (meshSequence A i) n ⟶ gridComplex (meshSequence A i) n) (r : ℤ) :
    (chainModel A i).X r ⟶ (chainModel A i).X r :=
  basedTensorHom cp2Complex_dim_neg_ga cp2Complex_dim_neg_ga 0 0
      (fun s => a.f s ≫ eqToHom (congrArg (gridComplex (meshSequence A i) n).X (add_zero s).symm))
      (idDeg0 cp2Complex) r ≫
    eqToHom (congrArg (chainModel A i).X (show r + (0 + 0) = r by ring))

/-- The *group approximation* `a_{g,i}` in degree `r`: the identity if `g = 0`, and
`a_i[\widehat{r_i(g)}] ⊗ 1_P` otherwise. -/
noncomputable def groupApprox (A : LocalDatum p n D ρplus) (i : ℕ) (g : ZMod (p ^ i)) (r : ℤ) :
    (chainModel A i).X r ⟶ (chainModel A i).X r :=
  if g = 0 then 𝟙 _ else
    chainTensorOneP A i (chainApprox A i (completedMap_mem_trackFamily A (rep p i g))) r

end HSP.ChainModels
