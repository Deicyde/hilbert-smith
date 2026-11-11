import Mathlib
import HilbertSmithPaper.ChainModels.Approximations.CompletedMap
import HilbertSmithPaper.LocalData.Control.RepresentativeMap

/-!
# Completed representative

The completed representative of `g ∈ ℤ/p^i` is the completed map `\widehat{r_i(g)}` of its
representative `r_i(g) ∈ ℤ_p`.

## Encoding

`completedRep A i g` (the declaration of the article) is `completedMap A (rep p i g)`.
-/

namespace HSP.ChainModels

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The completed representative `\widehat{r_i(g)}` of `g ∈ ℤ/p^i`. -/
noncomputable def completedRep (A : LocalDatum p n D ρplus) (i : ℕ) (g : ZMod (p ^ i)) :
    Torus n → Torus n :=
  completedMap A (rep p i g)

end HSP.ChainModels
