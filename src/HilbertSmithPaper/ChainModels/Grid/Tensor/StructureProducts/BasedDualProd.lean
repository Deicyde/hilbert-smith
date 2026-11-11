import Mathlib
import HilbertSmithPaper.ChainModels.Grid.BasedComplexTensor

/-!
# Product of duality maps in explicit bases

For degree-`0` maps `f_r : C_r → C^*_{m-r}` and `g_r : E_r → E^*_{m'-r}`, `m + m' = k`, the map `Ξ^{-1} ∘ (f ⊗ g) : C ⊗ E → (C ⊗ E)^{k-*}`: the block from `C_a ⊠ E_c` to the dual of `C_{m-a} ⊠ E_{m'-c}` is `(-1)^{c(a+m)} f_a ⊠ g_c`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Kronecker

namespace HSP.ChainModels

open FreeQ DualCat

variable (C E : ChainComplex FreeQ ℤ) (hE : ∀ q < 0, (E.X q).dim = 0)

/-- The degree-`0` map `Ξ^{-1} ∘ (f ⊗ g) : C ⊗ E → (C ⊗ E)^{k-*}` of `f_r : C_r → C^*_{m-r}` and
`g_r : E_r → E^*_{m'-r}`, `m + m' = k`: the block from `C_a ⊠ E_c` to the dual of
`C_{m-a} ⊠ E_{m'-c}` is `(-1)^{c(a+m)} f_a ⊠ g_c`. -/
noncomputable def basedDualProd (m m' k : ℤ) (hk : m + m' = k)
    (f : ∀ r, C.X r ⟶ dual (C.X (m - r))) (g : ∀ r, E.X r ⟶ dual (E.X (m' - r))) (r : ℤ) :
    (basedComplexTensor C E hE).X r ⟶ dual ((basedComplexTensor C E hE).X (k - r)) :=
  ∑ a : Fin (r.toNat + 1), ∑ a' : Fin ((k - r).toNat + 1),
    if h : ((a' : ℕ) : ℤ) = m - (a : ℕ) then
      ((r - (a : ℕ)) * ((a : ℕ) + m)).negOnePow •
        (blockProj (tensorSummandDim C E r) a ≫
          basedKron (f (a : ℕ)) (g (r - (a : ℕ))) ≫
          eqToHom (by
            simp only [dual_eq, tensorSummandDim]
            rw [h, show k - r - (m - ((a : ℕ) : ℤ)) = m' - (r - ((a : ℕ) : ℤ)) by omega]) ≫
          blockInc (tensorSummandDim C E (k - r)) a')
    else 0

end HSP.ChainModels
