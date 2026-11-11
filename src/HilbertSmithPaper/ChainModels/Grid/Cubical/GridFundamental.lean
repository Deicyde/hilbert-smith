import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Cubical.CubicalTorusGrid
import HilbertSmithPaper.ChainModels.Grid.Cubical.CircleFundamental

/-!
# Fundamental chain of the grid complex

The fundamental chain `z(k) = ⊗_j ∑_w e_w ∈ C(k)_n`: in `(C(k) ⊗ S_k)_{n+1}` it lies in the
summand `C(k)_n ⊠ S_{k,1}`.

## Encoding

`gridFundamental k n` (the declaration of the article) is a column, a morphism from `ℚ = ⟨1⟩`, by
recursion on `n`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.ChainModels

open FreeQ

/-- The *fundamental chain* `z(k) = ⊗_j ∑_w e_w ∈ C(k)_n`, as a column: in `(C(k) ⊗ S_k)_{n+1}`
it lies in the summand `C(k)_n ⊠ S_{k,1}`. -/
noncomputable def gridFundamental (k : ℕ) : ∀ n : ℕ, (⟨1⟩ : FreeQ) ⟶ (gridComplex k n).X n
  | 0 => ofMatrix (Matrix.of fun _ _ => 1)
  | n + 1 =>
    basedKron (gridFundamental k n)
        (circleFundamental k ≫ eqToHom (congrArg (circleComplex k).X (by push_cast; ring))) ≫
      blockInc (tensorSummandDim (gridComplex k n) (circleComplex k) ((n + 1 : ℕ) : ℤ))
        ⟨n, by simp⟩

end HSP.ChainModels
