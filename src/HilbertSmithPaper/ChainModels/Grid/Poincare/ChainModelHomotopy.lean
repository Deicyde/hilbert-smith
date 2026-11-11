import Mathlib
import HilbertSmithPaper.ChainModels.Grid.ChainModelDuality
import HilbertSmithPaper.ChainModels.Grid.Poincare.ChainModelH
import HilbertSmithPaper.ChainModels.Grid.Poincare.GridDimNeg
import HilbertSmithPaper.ChainModels.Grid.Poincare.Cp2Inverse
import HilbertSmithPaper.ChainModels.Grid.Poincare.GridInverse
import HilbertSmithPaper.ChainModels.Grid.Poincare.TensorHomotopy
import HilbertSmithPaper.ChainModels.Grid.Tensor.TensorHomAddRight
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.DualProdCompStrProd
import HilbertSmithPaper.LTheory.Base.Complexes.DualComplex

/-!
# The chain-model homotopy

`φ_i b_i - 1 = dH_i + H_i d` on `D_i`.

## Proof

The composite of a product of duality maps and a product of structures is the tensor of the
factorwise composites,
so `φ_i b_i = A_n ⊗ φ_P b_P = A_n ⊗ 1` with `A_n = φ_n b_n` on the grid. By the
tensor product of homotopies, `A_{n+1} - 1 = dH^{(n+1)} + H^{(n+1)}d` from the same for `A_n` and 
`A - 1 = dK + Kd` (circle duality (3)), starting from `A_0 = 1`, `H^{(0)} = 0`; once more with
`g = 1`, `k = 0` it gives `φ_i b_i - 1 = dH_i + H_i d`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.ChainModels

open FreeQ DualCat

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

private lemma grid_homotopy (k : ℕ) : ∀ (n : ℕ) (r : ℤ),
    gridDualMap k n r ≫ gridStructure k n ⟨(r, (n : ℤ) - r), by ring⟩ - 𝟙 _ =
      gridH k n r ≫ (gridComplex k n).d (r + 1) r +
        (gridComplex k n).d r (r - 1) ≫ gridH k n (r - 1) ≫
          eqToHom (congrArg (gridComplex k n).X (by ring))
  | 0, r => by
    rw [show gridDualMap k 0 r ≫ gridStructure k 0 ⟨(r, ((0 : ℕ) : ℤ) - r), by ring⟩ = 𝟙 _ from
      gridDualMap_comp_gridStructureU k 0 r]
    simp [gridH]
  | n + 1, r => by
    have e := basedDualProd_comp_basedStrProd (circleComplex_dim_neg k) (gridComplex_dim_neg k n)
        n 1
      ((n + 1 : ℕ) : ℤ) (by push_cast; ring) (gridDualMap k n) (circleB k) (gridStructure k n)
      (circlePhiSym k) r
    have T := basedTensorHom_homotopy (gridComplex_dim_neg k n) (circleComplex_dim_neg k)
      (fun a => gridDualMap k n a ≫ gridStructure k n ⟨(a, (n : ℤ) - a), by ring⟩ ≫
        eqToHom (congrArg (gridComplex k n).X (add_zero a).symm)) (circleA k) (gridH k n) (circleK
            k)
      (fun a => by
        simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
        exact grid_homotopy k n a)
      (fun c => by
        simp only [circleA, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
        exact (circle_duality k).2.2.1 c)
      (gridH k (n + 1)) (fun _ => rfl) r
    rw [show gridDualMap k (n + 1) r ≫
        gridStructure k (n + 1) ⟨(r, ((n + 1 : ℕ) : ℤ) - r), by ring⟩ = _
      from e]
    exact T

/-- *The chain-model homotopy*: `φ_i b_i - 1 = dH_i + H_i d` on `D_i`. -/
theorem chainModel_homotopy (A : LocalDatum p n D ρplus) (i : ℕ) :
    ∀ r : ℤ, (chainModelDuality A i).b r ≫
          (chainModelDuality A i).φ ⟨(r, (n + 4 : ℕ) - r), by ring⟩ - 𝟙 _ =
        chainModelH A i r ≫ (chainModel A i).d (r + 1) r +
          (chainModel A i).d r (r - 1) ≫ chainModelH A i (r - 1) ≫
            eqToHom (congrArg (chainModel A i).X (by ring)) := by
  intro r
  have e := basedDualProd_comp_basedStrProd cp2Complex_dim_neg (gridComplex_dim_neg _ n) n 4
    ((n + 4 : ℕ) : ℤ) (by push_cast; ring) (gridDualMap (meshSequence A i) n) cp2Inverse.f
    (gridStructure (meshSequence A i) n) cp2Structure r
  have hP : (fun c => cp2Inverse.f c ≫ cp2Structure ⟨(c, 4 - c), by ring⟩ ≫
      eqToHom (congrArg cp2Complex.X (add_zero c).symm)) = idDeg0 cp2Complex :=
    funext fun c => by rw [← Category.assoc, (cp2Inverse_comp_cp2Structure c).1,
        Category.id_comp]; rfl
  rw [hP] at e
  have hz : ∀ r, basedTensorHom cp2Complex_dim_neg cp2Complex_dim_neg 0 1
      (idDeg0 (gridComplex (meshSequence A i) n)) 0 r = 0 := fun r => by
    have := basedTensorHom_add_right cp2Complex_dim_neg cp2Complex_dim_neg 0 1
      (idDeg0 (gridComplex (meshSequence A i) n)) 0 0 r
    rw [add_zero] at this
    exact add_left_cancel (this.symm.trans (add_zero _).symm)
  have T := basedTensorHom_homotopy (gridComplex_dim_neg _ n) cp2Complex_dim_neg
    (fun a => gridDualMap (meshSequence A i) n a ≫
      gridStructure (meshSequence A i) n ⟨(a, (n : ℤ) - a), by ring⟩ ≫
        eqToHom (congrArg (gridComplex (meshSequence A i) n).X (add_zero a).symm))
    (idDeg0 cp2Complex) (gridH (meshSequence A i) n) 0
    (fun a => by
      simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
      exact grid_homotopy _ n a)
    (fun c => by simp [idDeg0])
    (chainModelH A i) (fun r => by rw [hz r, zero_comp, add_zero]; rfl) r
  rw [show (chainModelDuality A i).b r ≫
      (chainModelDuality A i).φ ⟨(r, ((n + 4 : ℕ) : ℤ) - r), by ring⟩ = _ from e]
  exact T

end HSP.ChainModels
