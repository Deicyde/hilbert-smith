import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Model.ChainModel
import HilbertSmithPaper.ChainModels.Grid.Cubical.GridFundamental
import HilbertSmithPaper.ChainModels.Grid.Cp2.Cp2Fundamental

/-!
# Fundamental cycle of the chain model

The fundamental cycle `z_i = z(k_i) ⊗ e_4 ∈ (D_i)_{n+4}`, in the summand `C(k_i)_n ⊠ P_4`.

## Encoding

`chainModelFundamental A i` (the declaration of the article) is a column, a morphism from
`ℚ = ⟨1⟩`.
-/

open CategoryTheory

namespace HSP.ChainModels

open FreeQ

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The fundamental cycle `z_i = z(k_i) ⊗ e_4 ∈ (D_i)_{n+4}`, as a column. -/
noncomputable def chainModelFundamental (A : LocalDatum p n D ρplus) (i : ℕ) :
    (⟨1⟩ : FreeQ) ⟶ (chainModel A i).X ((n + 4 : ℕ) : ℤ) :=
  basedKron (gridFundamental (meshSequence A i) n)
      (cp2Fundamental ≫ eqToHom (congrArg cp2Complex.X (by push_cast; ring))) ≫
    blockInc (tensorSummandDim (gridComplex (meshSequence A i) n) cp2Complex ((n + 4 : ℕ) : ℤ))
      ⟨n, by omega⟩

end HSP.ChainModels
