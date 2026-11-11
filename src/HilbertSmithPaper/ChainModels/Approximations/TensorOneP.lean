import Mathlib
import HilbertSmithPaper.ChainModels.Grid.ChainModel
import HilbertSmithPaper.ChainModels.Grid.Tensor.BasedTensorHom
import HilbertSmithPaper.ChainModels.Grid.Tensor.IdDeg0
import HilbertSmithPaper.ChainModels.Grid.Cp2DimNeg
import HilbertSmithPaper.ChainModels.Grid.Cubical.CubicalTorusGrid

/-!
# Tensoring with `1_P`

For a map `f` of degree `m` of `C(k_i)`, `f ⊗ 1_P` is the map of degree `m` of
`D_i = C(k_i) ⊗ P`: the tensor of maps with the identity of `P` (of degree `0`), in the explicit
bases of the tensor product of based complexes.

## Encoding

`tensorOneP A i m f r` (the declaration of the article) is the degree-`r` component
`(D_i)_r → (D_i)_{r+m}`, `basedTensorHom` of `f` and `idDeg0 P`, followed by the identification
`r + (m + 0) = r + m`.
-/

open CategoryTheory

namespace HSP.ChainModels

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The map `f ⊗ 1_P` of degree `m` of `D_i = C(k_i) ⊗ P`, for a map `f` of degree `m` of
`C(k_i)`. -/
noncomputable def tensorOneP (A : LocalDatum p n D ρplus) (i : ℕ) (m : ℤ)
    (f : ∀ r, (gridComplex (meshSequence A i) n).X r ⟶ (gridComplex (meshSequence A i) n).X (r + m))
    (r : ℤ) : (chainModel A i).X r ⟶ (chainModel A i).X (r + m) :=
  basedTensorHom cp2Complex_dim_neg cp2Complex_dim_neg m 0 f (idDeg0 cp2Complex) r ≫
    eqToHom (congrArg (chainModel A i).X (show r + (m + 0) = r + m by ring))

end HSP.ChainModels
