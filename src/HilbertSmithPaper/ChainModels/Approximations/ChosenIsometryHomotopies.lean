import Mathlib
import HilbertSmithPaper.ChainModels.Approximations.IsometryHomotopies
import HilbertSmithPaper.ChainModels.Grid.Cp2DimNeg
import HilbertSmithPaper.ChainModels.Grid.Cubical.CubicalTorusGrid

/-!
# Chosen isometry homotopies

Fix `U^T_g` given by isometry homotopies for all `i` and `g`, and put `U_g = U^T_g ⊗ φ_P`.

## Encoding

`isometryHomotopy A i g` (the declaration of the article) is `U_g ∈ M(D_i)_{N+1}`, the external
product `basedStrProd` of the `U^T_g` chosen (`Exists.choose`) from `isometry_homotopies` with
`φ_P`; `isometryHomotopy_spec` records its properties.
-/

open CategoryTheory
open scoped NNReal

namespace HSP.ChainModels

open FreeQ DualCat

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The chosen isometry homotopy `U_g = U^T_g ⊗ φ_P ∈ M(D_i)_{N+1}`. -/
noncomputable def isometryHomotopy (A : LocalDatum p n D ρplus) (i : ℕ) (g : ZMod (p ^ i)) :
    (StructureCx (chainModel A i)).X (((n + 4 : ℕ) : ℤ) + 1) :=
  basedStrProd (gridComplex (meshSequence A i) n) cp2Complex cp2Complex_dim_neg
    ((n : ℤ) + 1) 4 (((n + 4 : ℕ) : ℤ) + 1) (by push_cast; ring)
    (isometry_homotopies A i g).choose cp2Structure

/-- The properties of the chosen isometry homotopies. -/
lemma isometryHomotopy_spec (A : LocalDatum p n D ρplus) (i : ℕ) (g : ZMod (p ^ i)) :
    (∀ x : {x : ℤ × ℤ // x.1 + x.2 = ((n + 4 : ℕ) : ℤ)},
      (StructureCx (chainModel A i)).d (((n + 4 : ℕ) : ℤ) + 1) ((n + 4 : ℕ) : ℤ)
          (isometryHomotopy A i g) x =
        dualHom (groupApprox A i g x.1.2) ≫ (chainModelDuality A i).φ x ≫
            groupApprox A i g x.1.1 - (chainModelDuality A i).φ x) ∧
    ∀ x : {x : ℤ × ℤ // x.1 + x.2 = ((n + 4 : ℕ) : ℤ) + 1},
      (prop (chainModelLabel A i x.1.2) (chainModelLabel A i x.1.1) (isometryHomotopy A i g x) :
        ℝ) ≤
        (3 * trackModulus A (2 * (4 / (meshSequence A i : ℝ))) +
          8 * (4 / (meshSequence A i : ℝ))) + 2 * (4 / (meshSequence A i : ℝ)) :=
  (isometry_homotopies A i g).choose_spec

end HSP.ChainModels
