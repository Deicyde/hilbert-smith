import Mathlib
import HilbertSmithPaper.ChainModels.Grid.ChainModelDuality
import HilbertSmithPaper.ChainModels.Grid.Poincare.GridFactor.GridStructureU
import HilbertSmithPaper.ChainModels.Grid.Poincare.GridFactor.GridDimNeg
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.DualProdCompStrProd
import HilbertSmithPaper.ChainModels.Grid.Tensor.TensorHomId

/-!
# The grid duality map inverts the unsymmetrized grid structure

`b_r ≫ (φ^u_n)_{r,n-r} = 1` on `C(k)_r` for the iterated duality map `b = b ⊗ ⋯ ⊗ b` and the
unsymmetrized grid structure.

## Proof

Induction on `n`: on the unit complex both are the identity of `ℚ`; the composite of a product of
duality maps and a product of structures is the tensor of the factorwise composites, which are
identities by induction and circle duality (1), and the tensor of identities is the identity.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.ChainModels

open FreeQ DualCat

private lemma unit_inverse (r : ℤ) :
    unitDualMap r ≫ unitStructure ⟨(r, 0 - r), by ring⟩ = 𝟙 _ := by
  refine Matrix.ext fun a b => ?_
  by_cases hr : r = 0
  · subst hr
    revert a b
    change ∀ a b : Fin 1, (∑ c : Fin 1, (1 : ℚ) * 1) = (1 : Matrix (Fin 1) (Fin 1) ℚ) a b
    intro a b
    fin_cases a; fin_cases b
    simp
  · have hd : unitDim r = 0 := by
      rcases r with (_ | r) | r
      · exact absurd rfl hr
      · rfl
      · rfl
    exact (Fin.cast hd a).elim0

/-- *The grid duality map inverts the unsymmetrized grid structure*: `φ^u_n b = 1`. -/
lemma gridDualMap_comp_gridStructureU (k : ℕ) : ∀ (n : ℕ) (r : ℤ),
    gridDualMap k n r ≫ gridStructureU k n ⟨(r, (n : ℤ) - r), by ring⟩ = 𝟙 _
  | 0, r => unit_inverse r
  | n + 1, r => by
    have e := basedDualProd_comp_basedStrProd (circleComplex_dim_neg k) (gridComplex_dim_neg k n)
        n 1
      ((n + 1 : ℕ) : ℤ) (by push_cast; ring) (gridDualMap k n) (circleB k) (gridStructureU k n)
      (circlePhi k) r
    have h1 : (fun a => gridDualMap k n a ≫ gridStructureU k n ⟨(a, (n : ℤ) - a), by ring⟩ ≫
        eqToHom (congrArg (gridComplex k n).X (add_zero a).symm)) = idDeg0 (gridComplex k n) :=
      funext fun a => by rw [← Category.assoc, gridDualMap_comp_gridStructureU k n a,
          Category.id_comp]; rfl
    have h2 : (fun c => circleB k c ≫ circlePhi k ⟨(c, 1 - c), by ring⟩ ≫
        eqToHom (congrArg (circleComplex k).X (add_zero c).symm)) = idDeg0 (circleComplex k) :=
      funext fun c => by rw [← Category.assoc, ((circle_duality k).1.2 c).2, Category.id_comp]; rfl
    rw [h1, h2, basedTensorHom_id, eqToHom_trans, eqToHom_refl] at e
    exact e

end HSP.ChainModels
