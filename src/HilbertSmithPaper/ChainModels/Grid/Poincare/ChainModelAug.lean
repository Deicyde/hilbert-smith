import Mathlib
import HilbertSmithPaper.ChainModels.Grid.ChainModel
import HilbertSmithPaper.ChainModels.Grid.Cubical.GridAug
import HilbertSmithPaper.ChainModels.Grid.Cp2.Cp2Aug

/-!
# The augmentation of the chain model

`ε = ε^{⊗n} ⊠ ε_P : (D_i)_0 → ℚ`.
-/

open CategoryTheory

namespace HSP.ChainModels

open FreeQ DualCat

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The augmentation `ε = ε^{⊗n} ⊠ ε_P : (D_i)_0 → ℚ`. -/
noncomputable def chainModelAug (A : LocalDatum p n D ρplus) (i : ℕ) :
    (chainModel A i).X 0 ⟶ (⟨1⟩ : FreeQ) :=
  blockProj _ (0 : Fin 1) ≫ basedKron (gridAug (meshSequence A i) n) cp2Aug

end HSP.ChainModels
