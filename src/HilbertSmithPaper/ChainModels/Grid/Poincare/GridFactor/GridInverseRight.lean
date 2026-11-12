import Mathlib
import HilbertSmithPaper.ChainModels.Grid.ChainModelDuality
import HilbertSmithPaper.ChainModels.Grid.Poincare.GridFactor.GridDualMap
import HilbertSmithPaper.ChainModels.Grid.Poincare.GridFactor.GridStructureU
import HilbertSmithPaper.ChainModels.Grid.Poincare.GridFactor.GridDimNeg
import HilbertSmithPaper.ChainModels.Grid.Poincare.GridFactor.IdDualDeg0
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.StrProdCompDualProd
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.DualTensorHomId

/-!
# The unsymmetrized grid structure inverts the grid duality map

`(φ^u_n)_{r,n-r} ≫ b_r = 1` on `(C(k)^{n-*})_r` for the unsymmetrized grid structure and the
iterated duality map `b = b ⊗ ⋯ ⊗ b`.

## Proof

Induction on `n`: on the unit complex both are the identity of `ℚ`; a product of duality maps after
a product of structures is the dual tensor of the factorwise composites, which are identities by
induction and circle duality (1), and the dual tensor of identities is the identity.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.ChainModels

open FreeQ DualCat

private lemma unit_inverse_right (k : ℕ) (r : ℤ) :
    unitStructure ⟨(r, 0 - r), by ring⟩ ≫ gridDualMap k 0 r = 𝟙 _ := by
  refine Matrix.ext fun a b => ?_
  by_cases hr : r = 0
  · subst hr
    revert a b
    change ∀ a b : Fin 1, (∑ c : Fin 1, (1 : ℚ) * 1) = (1 : Matrix (Fin 1) (Fin 1) ℚ) a b
    intro a b
    fin_cases a; fin_cases b
    simp
  · have hd : (unitComplex.X (0 - r)).dim = 0 := unitComplex_X_dim_of_ne (by omega)
    exact (Fin.cast hd a).elim0

/-- *The unsymmetrized grid structure inverts the grid duality map*: `b φ^u_n = 1`. -/
lemma gridStructureU_comp_gridDualMap (k : ℕ) : ∀ (n : ℕ) (r : ℤ),
    gridStructureU k n ⟨(r, (n : ℤ) - r), by ring⟩ ≫ gridDualMap k n r = 𝟙 _
  | 0, r => unit_inverse_right k r
  | n + 1, r => by
    have e := basedStrProd_comp_basedDualProd (circleComplex_dim_neg k) (gridComplex_dim_neg k n)
        n 1
      ((n + 1 : ℕ) : ℤ) (by push_cast; ring) (gridDualMap k n) (circleB k) (gridStructureU k n)
      (circlePhi k) r
    have h1 : (fun t => gridStructureU k n ⟨(t, (n : ℤ) - t), by ring⟩ ≫ gridDualMap k n t ≫
        eqToHom (congrArg (fun u => dual ((gridComplex k n).X ((n : ℤ) - u))) (add_zero t).symm)) =
        idDualDeg0 (gridComplex k n) n :=
      funext fun t => by rw [← Category.assoc, gridStructureU_comp_gridDualMap k n t,
          Category.id_comp]; rfl
    have h2 : (fun t => circlePhi k ⟨(t, 1 - t), by ring⟩ ≫ circleB k t ≫
        eqToHom (congrArg (fun u => dual ((circleComplex k).X (1 - u))) (add_zero t).symm)) =
        idDualDeg0 (circleComplex k) 1 :=
      funext fun t => by rw [← Category.assoc, ((circle_duality k).1.2 t).1, Category.id_comp]; rfl
    rw [h1, h2, basedDualTensorHom_id, eqToHom_trans, eqToHom_refl] at e
    exact e

end HSP.ChainModels
