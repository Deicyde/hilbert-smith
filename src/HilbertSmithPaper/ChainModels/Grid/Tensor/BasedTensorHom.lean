import Mathlib
import HilbertSmithPaper.ChainModels.Grid.BasedComplexTensor

/-!
# Tensor of maps of based complexes

For maps `f_r : C_r → C'_{r+d}` and `g_r : E_r → E'_{r+e}` of complexes of based vector spaces
(with `E`, `E'` in degrees `≥ 0`), the tensor `f ⊗ g : C ⊗ E → C' ⊗ E'` of degree `d + e` is
`(f ⊗ g)(x ⊗ y) = (-1)^{e|x|} f(x) ⊗ g(y)`, computed in the explicit bases of the tensor product
of based complexes.

## Encoding

`basedTensorHom` is given by its blocks: from the summand `C_a ⊠ E_{r-a}` of degree `r` to the
summand `C'_{a+d} ⊠ E'_{r-a+e}` of degree `r + (d + e)` it is `(-1)^{e a} f_a ⊠ g_{r-a}`, with the
identity transport of the summand, and all other blocks are `0`.
-/

open CategoryTheory

namespace HSP.ChainModels

open FreeQ

variable {C C' E E' : ChainComplex FreeQ ℤ}

/-- The tensor `f ⊗ g` of maps of degrees `d` and `e`: on `C_a ⊠ E_c` it is
`(-1)^{e a} f_a ⊠ g_c` into `C'_{a+d} ⊠ E'_{c+e}`. -/
noncomputable def basedTensorHom (hE : ∀ q < 0, (E.X q).dim = 0)
    (hE' : ∀ q < 0, (E'.X q).dim = 0) (d e : ℤ) (f : ∀ r, C.X r ⟶ C'.X (r + d))
    (g : ∀ r, E.X r ⟶ E'.X (r + e)) (r : ℤ) :
    (basedComplexTensor C E hE).X r ⟶ (basedComplexTensor C' E' hE').X (r + (d + e)) :=
  ∑ a : Fin (r.toNat + 1), ∑ a' : Fin ((r + (d + e)).toNat + 1),
    if h : ((a' : ℕ) : ℤ) = (a : ℕ) + d then
      (e * (a : ℕ)).negOnePow •
        (blockProj (tensorSummandDim C E r) a ≫ basedKron (f (a : ℕ)) (g (r - (a : ℕ))) ≫
          eqToHom (by
            simp only [tensorSummandDim]
            rw [h, show r + (d + e) - (((a : ℕ) : ℤ) + d) = r - ((a : ℕ) : ℤ) + e by ring]) ≫
          blockInc (tensorSummandDim C' E' (r + (d + e))) a')
    else 0

end HSP.ChainModels
