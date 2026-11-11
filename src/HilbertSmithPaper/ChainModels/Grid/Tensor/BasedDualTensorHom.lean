import Mathlib
import HilbertSmithPaper.ChainModels.Grid.BasedComplexTensor

/-!
# Dual tensor of maps of based complexes

For maps `F` of `C^{m-*}` of degree `d` and `G` of `E^{m'-*}` of degree `e`, `m + m' = k`, the map
`Ξ^{-1}(F ⊗ G)Ξ` of `(C ⊗ E)^{k-*}`, where `Ξ : (C ⊗ E)^{k-*} ≅ C^{m-*} ⊗ E^{m'-*}` carries the
signs `s(a,b) = (-1)^{b(a+m)}`.

## Encoding

`basedDualTensorHom` is given by its blocks: from the dual of `C_{m-a} ⊠ E_{m'-b}` to the dual of
`C_{m-a-d} ⊠ E_{m'-b-e}` it is `s(a+d, b+e) (-1)^{e a} s(a, b) F_a ⊠ G_b`, with identity
transports, and all other blocks are `0`.
-/

open CategoryTheory

namespace HSP.ChainModels

open FreeQ DualCat

variable {C E : ChainComplex FreeQ ℤ}

/-- The map `Ξ^{-1}(F ⊗ G)Ξ` of `(C ⊗ E)^{k-*}`, `m + m' = k`, for maps `F` of `C^{m-*}` and `G`
of `E^{m'-*}` of degrees `d`, `e`: from the dual of `C_{m-a} ⊠ E_{m'-b}` to the dual of
`C_{m-a-d} ⊠ E_{m'-b-e}` it is `s(a+d,b+e) (-1)^{e a} s(a,b) F_a ⊠ G_b`. -/
noncomputable def basedDualTensorHom (hE : ∀ q < 0, (E.X q).dim = 0) (m m' k : ℤ)
    (hk : m + m' = k) (d e : ℤ) (F : ∀ r, dual (C.X (m - r)) ⟶ dual (C.X (m - (r + d))))
    (G : ∀ r, dual (E.X (m' - r)) ⟶ dual (E.X (m' - (r + e)))) (r : ℤ) :
    dual ((basedComplexTensor C E hE).X (k - r)) ⟶
      dual ((basedComplexTensor C E hE).X (k - (r + (d + e)))) :=
  ∑ p : Fin ((k - r).toNat + 1), ∑ p' : Fin ((k - (r + (d + e))).toNat + 1),
    if h : ((p' : ℕ) : ℤ) = (p : ℕ) - d then
      (((r - (m - (p : ℕ))) + e) * ((m - (p : ℕ)) + d + m) + e * (m - (p : ℕ)) +
          (r - (m - (p : ℕ))) * ((m - (p : ℕ)) + m)).negOnePow •
        (blockProj (tensorSummandDim C E (k - r)) p ≫
          eqToHom (by
            simp only [tensorSummandDim, dual_eq]
            rw [show m - (m - ((p : ℕ) : ℤ)) = ((p : ℕ) : ℤ) by ring,
              show m' - (r - (m - ((p : ℕ) : ℤ))) = k - r - ((p : ℕ) : ℤ) by omega]) ≫
          basedKron (F (m - (p : ℕ))) (G (r - (m - (p : ℕ)))) ≫
          eqToHom (by
            simp only [tensorSummandDim, dual_eq]
            rw [h, show m - (m - ((p : ℕ) : ℤ) + d) = ((p : ℕ) : ℤ) - d by ring,
              show m' - (r - (m - ((p : ℕ) : ℤ)) + e) = k - (r + (d + e)) - (((p : ℕ) : ℤ) - d) by
                omega]) ≫
          blockInc (tensorSummandDim C E (k - (r + (d + e)))) p')
    else 0

end HSP.ChainModels
