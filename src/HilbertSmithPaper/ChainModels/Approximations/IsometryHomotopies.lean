import Mathlib
import HilbertSmithPaper.ChainModels.Approximations.GroupApprox
import HilbertSmithPaper.ChainModels.Grid.ChainModelDuality
import HilbertSmithPaper.ChainModels.Grid.ChainModelPoincare
import HilbertSmithPaper.ChainModels.Grid.Cp2.Cp2DimNeg
import HilbertSmithPaper.ChainModels.Grid.Cubical.CubicalTorusGrid
import HilbertSmithPaper.ChainModels.Grid.Cp2.Cp2Structure
import HilbertSmithPaper.ChainModels.Grid.Cp2.Cp2Complex
import HilbertSmithPaper.ChainModels.Grid.Model.ChainModelLabel

/-!
# Isometry homotopies

With `s_i = 3ω(2h_i) + 8h_i`, for `g ∈ G_i` there are `U^T_g ∈ M(C(k_i))_{n+1}` such that
`U_g = U^T_g ⊗ φ_P ∈ M(D_i)_{N+1}` satisfies `a_g φ_i a_g^* - φ_i = dU_g + U_g d` and has
`d_∞`-propagation at most `s_i + 2h_i` in torus labels.

## Encoding

* `U_g = U^T_g ⊗ φ_P` is the external product `basedStrProd` (as for `φ_i`), `N = n + 4`.
* `dU_g + U_g d`, with `d` the differentials of `D_i` and `D_i^{N-*}`, is the differential `∂U_g`
  of the structure complex `M(D_i)` (`StructureCx.d_apply`).
* `a_g φ_i a_g^*` is given componentwise: on `(D_i^{N-*})_{N-q} = (D_i)_q^*` into `(D_i)_p`,
  `p + q = N`, it is `a_g^* ≫ φ_i ≫ a_g` with `a_g^* = dualHom (a_g)_q`.
* Torus labels of cells and duals are `chainModelLabel`; propagation is `prop` for `d_∞`.
* The chosen `U_g` is `isometryHomotopy` (chosen isometry homotopies).
-/

open CategoryTheory
open scoped NNReal

namespace HSP.ChainModels

open FreeQ DualCat

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- **Isometry homotopies.** For `g ∈ G_i` there is `U^T_g ∈ M(C(k_i))_{n+1}` such that
`U_g = U^T_g ⊗ φ_P` satisfies `a_g φ_i a_g^* - φ_i = dU_g + U_g d` and has `d_∞`-propagation at
most `s_i + 2h_i`, `s_i = 3ω(2h_i) + 8h_i`, `h_i = 4/k_i`. -/
theorem isometry_homotopies (A : LocalDatum p n D ρplus) (i : ℕ) (g : ZMod (p ^ i)) :
    ∃ UT : (StructureCx (gridComplex (meshSequence A i) n)).X ((n : ℤ) + 1),
      (∀ x : {x : ℤ × ℤ // x.1 + x.2 = ((n + 4 : ℕ) : ℤ)},
        (StructureCx (chainModel A i)).d (((n + 4 : ℕ) : ℤ) + 1) ((n + 4 : ℕ) : ℤ)
            (basedStrProd (gridComplex (meshSequence A i) n) cp2Complex cp2Complex_dim_neg
              ((n : ℤ) + 1) 4 (((n + 4 : ℕ) : ℤ) + 1) (by push_cast; ring) UT cp2Structure) x =
          dualHom (groupApprox A i g x.1.2) ≫ (chainModelDuality A i).φ x ≫
              groupApprox A i g x.1.1 - (chainModelDuality A i).φ x) ∧
      ∀ x : {x : ℤ × ℤ // x.1 + x.2 = ((n + 4 : ℕ) : ℤ) + 1},
        (prop (chainModelLabel A i x.1.2) (chainModelLabel A i x.1.1)
          (basedStrProd (gridComplex (meshSequence A i) n) cp2Complex cp2Complex_dim_neg
            ((n : ℤ) + 1) 4 (((n + 4 : ℕ) : ℤ) + 1) (by push_cast; ring) UT cp2Structure x) :
          ℝ) ≤
          (3 * trackModulus A (2 * (4 / (meshSequence A i : ℝ))) +
            8 * (4 / (meshSequence A i : ℝ))) + 2 * (4 / (meshSequence A i : ℝ)) := by
  sorry

end HSP.ChainModels
