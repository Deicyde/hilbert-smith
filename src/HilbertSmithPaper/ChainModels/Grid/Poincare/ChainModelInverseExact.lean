import Mathlib
import HilbertSmithPaper.ChainModels.Grid.ChainModelDuality
import HilbertSmithPaper.ChainModels.Grid.Poincare.ChainModelStructureU
import HilbertSmithPaper.ChainModels.Grid.Poincare.GridDimNeg
import HilbertSmithPaper.ChainModels.Grid.Poincare.Cp2Inverse
import HilbertSmithPaper.ChainModels.Grid.Poincare.GridInverse
import HilbertSmithPaper.ChainModels.Grid.Poincare.IdDualDeg0
import HilbertSmithPaper.ChainModels.Grid.Tensor.TensorHomId
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.DualProdCompStrProd
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.StrProdCompDualProd
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.DualTensorHomId
import HilbertSmithPaper.LTheory.Base.Complexes.DualComplex

/-!
# The chain-model inverse is exact

`b_i` is the exact inverse of `(φ_i^u)_♮`: `φ_i^u b_i = 1` and `b_i φ_i^u = 1` in every degree.

## Proof

A product of duality maps after a product of structures is the tensor of the factorwise
composites, and a product of structures after a product of duality maps is their dual tensor.
The factors are identities: on the grid by induction on `n` (unit complex, circle duality (1)),
and for `CP²` directly. Tensors and dual tensors of identities are identities.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.ChainModels

open FreeQ DualCat

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

private lemma unit_inverse_right (r : ℤ) :
    unitStructure ⟨(r, 0 - r), by ring⟩ ≫ unitDualMap r = 𝟙 _ := by
  refine Matrix.ext fun a b => ?_
  by_cases hr : r = 0
  · subst hr
    revert a b
    change ∀ a b : Fin 1, (∑ c : Fin 1, (1 : ℚ) * 1) = (1 : Matrix (Fin 1) (Fin 1) ℚ) a b
    intro a b
    fin_cases a; fin_cases b
    simp
  · have hd : unitDim (0 - r) = 0 := by
      rcases r with (_ | r) | r
      · exact absurd rfl hr
      · rcases r with _ | r
        · rfl
        · rfl
      · rfl
    exact (Fin.cast hd a).elim0

private lemma grid_inverse_right (k : ℕ) : ∀ (n : ℕ) (r : ℤ),
    gridStructureU k n ⟨(r, (n : ℤ) - r), by ring⟩ ≫ gridDualMap k n r = 𝟙 _
  | 0, r => unit_inverse_right r
  | n + 1, r => by
    have e := basedStrProd_comp_basedDualProd (circleComplex_dim_neg k) (gridComplex_dim_neg k n)
        n 1
      ((n + 1 : ℕ) : ℤ) (by push_cast; ring) (gridDualMap k n) (circleB k) (gridStructureU k n)
      (circlePhi k) r
    have h1 : (fun t => gridStructureU k n ⟨(t, (n : ℤ) - t), by ring⟩ ≫ gridDualMap k n t ≫
        eqToHom (congrArg (fun u => dual ((gridComplex k n).X ((n : ℤ) - u))) (add_zero t).symm)) =
        idDualDeg0 (gridComplex k n) n :=
      funext fun t => by rw [← Category.assoc, grid_inverse_right k n t, Category.id_comp]; rfl
    have h2 : (fun t => circlePhi k ⟨(t, 1 - t), by ring⟩ ≫ circleB k t ≫
        eqToHom (congrArg (fun u => dual ((circleComplex k).X (1 - u))) (add_zero t).symm)) =
        idDualDeg0 (circleComplex k) 1 :=
      funext fun t => by rw [← Category.assoc, ((circle_duality k).1.2 t).1, Category.id_comp]; rfl
    rw [h1, h2, basedDualTensorHom_id, eqToHom_trans, eqToHom_refl] at e
    exact e

/-- *The chain-model inverse is exact*: `b_i` is the exact inverse of `(φ_i^u)_♮`: `φ_i^u b_i =
1` and `b_i φ_i^u = 1` in every degree. -/
theorem chainModel_inverse_exact (A : LocalDatum p n D ρplus) (i : ℕ) :
    ∀ r : ℤ, chainModelStructureU A i ⟨(r, (n + 4 : ℕ) - r), by ring⟩ ≫
          (chainModelDuality A i).b r = 𝟙 _ ∧
        (chainModelDuality A i).b r ≫ chainModelStructureU A i ⟨(r, (n + 4 : ℕ) - r), by ring⟩ =
          𝟙 _ := by
  intro r
  constructor
  · have e := basedStrProd_comp_basedDualProd cp2Complex_dim_neg (gridComplex_dim_neg _ n) n 4
      ((n + 4 : ℕ) : ℤ) (by push_cast; ring) (gridDualMap (meshSequence A i) n) cp2Inverse.f
      (gridStructureU (meshSequence A i) n) cp2Structure r
    have h1 : (fun t => gridStructureU (meshSequence A i) n ⟨(t, (n : ℤ) - t), by ring⟩ ≫
        gridDualMap (meshSequence A i) n t ≫ eqToHom (congrArg
          (fun u => dual ((gridComplex (meshSequence A i) n).X ((n : ℤ) - u))) (add_zero t).symm)) =
        idDualDeg0 (gridComplex (meshSequence A i) n) n :=
      funext fun t => by rw [← Category.assoc, grid_inverse_right _ n t, Category.id_comp]; rfl
    have h2 : (fun t => cp2Structure ⟨(t, 4 - t), by ring⟩ ≫ cp2Inverse.f t ≫
        eqToHom (congrArg (fun u => dual (cp2Complex.X (4 - u))) (add_zero t).symm)) =
        idDualDeg0 cp2Complex 4 :=
      funext fun t => by rw [← Category.assoc, (cp2Inverse_comp_cp2Structure t).2,
          Category.id_comp]; rfl
    rw [h1, h2, basedDualTensorHom_id, eqToHom_trans, eqToHom_refl] at e
    exact e
  · have e := basedDualProd_comp_basedStrProd cp2Complex_dim_neg (gridComplex_dim_neg _ n) n 4
      ((n + 4 : ℕ) : ℤ) (by push_cast; ring) (gridDualMap (meshSequence A i) n) cp2Inverse.f
      (gridStructureU (meshSequence A i) n) cp2Structure r
    have h1 : (fun a => gridDualMap (meshSequence A i) n a ≫
        gridStructureU (meshSequence A i) n ⟨(a, (n : ℤ) - a), by ring⟩ ≫
          eqToHom (congrArg (gridComplex (meshSequence A i) n).X (add_zero a).symm)) =
        idDeg0 (gridComplex (meshSequence A i) n) :=
      funext fun a => by
        rw [← Category.assoc, gridDualMap_comp_gridStructureU _ n a, Category.id_comp]; rfl
    have h2 : (fun c => cp2Inverse.f c ≫ cp2Structure ⟨(c, 4 - c), by ring⟩ ≫
        eqToHom (congrArg cp2Complex.X (add_zero c).symm)) = idDeg0 cp2Complex :=
      funext fun c => by rw [← Category.assoc, (cp2Inverse_comp_cp2Structure c).1,
          Category.id_comp]; rfl
    rw [h1, h2, basedTensorHom_id, eqToHom_trans, eqToHom_refl] at e
    exact e

end HSP.ChainModels
