import Mathlib
import HilbertSmithPaper.ChainModels.Grid.BasedComplexTensor

/-!
# Labels on a tensor product of based complexes

Given labels `l_C` on the basis of `C` and `l_E` on the basis of `E`, and a map `c`, the basis
vector `x ⊗ y` of the summand `C_p ⊠ E_{r-p}` of `(C ⊗ E)_r` is labelled `c (l_C x) (l_E y)`.

## Encoding

`tensorLabel hE lC lE c r a` (the declaration of the article) reads the summand `p` and the pair
`(x, y)` off the basis index `a` through `finSigmaFinEquiv` and `finProdFinEquiv`.
-/

namespace HSP.ChainModels

open FreeQ

/-- *Labels on a tensor product of based complexes*: the basis vector `x ⊗ y` of the summand
`C_p ⊠ E_{r-p}` of `(C ⊗ E)_r` is labelled `c (lC x) (lE y)`. -/
noncomputable def tensorLabel {X Y Z : Type*} {C E : ChainComplex FreeQ ℤ}
    (hE : ∀ q < 0, (E.X q).dim = 0) (lC : ∀ r, Fin (C.X r).dim → X)
    (lE : ∀ r, Fin (E.X r).dim → Y) (c : X → Y → Z) (r : ℤ)
    (a : Fin ((basedComplexTensor C E hE).X r).dim) : Z :=
  (fun s : (p : Fin (r.toNat + 1)) × Fin (tensorSummandDim C E r p) =>
    c (lC (s.1 : ℕ) (finProdFinEquiv.symm
        (s.2 : Fin ((C.X (s.1 : ℕ)).dim * (E.X (r - (s.1 : ℕ))).dim))).1)
      (lE (r - (s.1 : ℕ)) (finProdFinEquiv.symm
        (s.2 : Fin ((C.X (s.1 : ℕ)).dim * (E.X (r - (s.1 : ℕ))).dim))).2))
    (finSigmaFinEquiv.symm (a : Fin (∑ p, tensorSummandDim C E r p)))

end HSP.ChainModels
