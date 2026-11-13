import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.BasedVectorSpaces
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.BasedKron
import HilbertSmithPaper.LTheory.Localization.Products.DualityPairing

/-!
# Tensor product of based vector spaces

On the duality category `ℚ` of based vector spaces, `ℚ^a ⊠ ℚ^b = ℚ^{ab}` with
`e_i ⊠ e_j = e_{(i-1)b+j}`: the basis `Fin a × Fin b` is enumerated by `finProdFinEquiv`, which
sends `(i, j)` to `b * i + j` (0-based). For matrices `f`, `g`, `f ⊠ g` is the Kronecker product
`f ⊗ₖ g`, reindexed along this enumeration on rows and columns, so its entry in row
`(i, j)` and column `(k, l)` is `f i k * g j l`. With `κ` the identity, this is a duality pairing
`ℚ × ℚ → ℚ`: functoriality is the mixed-product rule, bilinearity holds entrywise, and
`(f ⊗ₖ g)ᵀ = fᵀ ⊗ₖ gᵀ` gives naturality of `κ = id`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Prod Kronecker

namespace HSP

open DualCat FreeQ

private lemma basedKron_comp {X X' X'' Y Y' Y'' : FreeQ} (f : X ⟶ X') (f' : X' ⟶ X'')
    (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
    basedKron (f ≫ f') (g ≫ g') = basedKron f g ≫ basedKron f' g' := by
  change ((toMatrix f' * toMatrix f) ⊗ₖ (toMatrix g' * toMatrix g)).submatrix
      finProdFinEquiv.symm finProdFinEquiv.symm =
    (toMatrix f' ⊗ₖ toMatrix g').submatrix finProdFinEquiv.symm finProdFinEquiv.symm *
      (toMatrix f ⊗ₖ toMatrix g).submatrix finProdFinEquiv.symm finProdFinEquiv.symm
  rw [Matrix.submatrix_mul_equiv, Matrix.mul_kronecker_mul]

private lemma kron_transpose {a a' b b' : ℕ} (A : Matrix (Fin a') (Fin a) ℚ)
    (B : Matrix (Fin b') (Fin b) ℚ) :
    ((A ⊗ₖ B).submatrix finProdFinEquiv.symm finProdFinEquiv.symm).transpose =
      (A.transpose ⊗ₖ B.transpose).submatrix finProdFinEquiv.symm finProdFinEquiv.symm := by
  rw [Matrix.transpose_submatrix, Matrix.kroneckerMap_transpose]

/-- The tensor product functor `⊠ : ℚ × ℚ ⥤ ℚ`. -/
private def basedTensor : FreeQ × FreeQ ⥤ FreeQ where
  obj P := ⟨P.1.dim * P.2.dim⟩
  map f := basedKron f.1 f.2
  map_id P := by
    change ((1 : Matrix (Fin P.1.dim) (Fin P.1.dim) ℚ) ⊗ₖ
        (1 : Matrix (Fin P.2.dim) (Fin P.2.dim) ℚ)).submatrix
      finProdFinEquiv.symm finProdFinEquiv.symm = 1
    rw [Matrix.one_kronecker_one, Matrix.submatrix_one_equiv]
  map_comp f g := basedKron_comp f.1 g.1 f.2 g.2

/-- **Tensor product of based vector spaces.** The Kronecker product `⊠` with `κ = id` is a
duality pairing `ℚ × ℚ → ℚ`. -/
def basedTensorPairing : DualityPairing FreeQ FreeQ FreeQ where
  tensor := basedTensor
  map_add_left f f' g := by
    change ((toMatrix f + toMatrix f') ⊗ₖ toMatrix g).submatrix _ _ =
      (toMatrix f ⊗ₖ toMatrix g).submatrix _ _ + (toMatrix f' ⊗ₖ toMatrix g).submatrix _ _
    rw [Matrix.add_kronecker, Matrix.submatrix_add]
    rfl
  map_add_right f g g' := by
    change (toMatrix f ⊗ₖ (toMatrix g + toMatrix g')).submatrix _ _ =
      (toMatrix f ⊗ₖ toMatrix g).submatrix _ _ + (toMatrix f ⊗ₖ toMatrix g').submatrix _ _
    rw [Matrix.kronecker_add, Matrix.submatrix_add]
    rfl
  map_smul_left c f g := by
    change ((c • toMatrix f) ⊗ₖ toMatrix g).submatrix _ _ =
      c • (toMatrix f ⊗ₖ toMatrix g).submatrix _ _
    rw [Matrix.smul_kronecker, Matrix.submatrix_smul]
    rfl
  map_smul_right c f g := by
    change (toMatrix f ⊗ₖ (c • toMatrix g)).submatrix _ _ =
      c • (toMatrix f ⊗ₖ toMatrix g).submatrix _ _
    rw [Matrix.kronecker_smul, Matrix.submatrix_smul]
    rfl
  κ N V := Iso.refl _
  κ_natural f g := by
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    exact kron_transpose (toMatrix f) (toMatrix g)
  κ_dual N V := by simp

/-- Non-vacuity of the duality-pairing interface. -/
private theorem dualityPairing_nonempty : Nonempty (DualityPairing FreeQ FreeQ FreeQ) :=
  ⟨basedTensorPairing⟩

end HSP
