import Mathlib
import HilbertSmithPaper.ChainModels.Approximations.ChosenProductHomotopies
import HilbertSmithPaper.ChainModels.Approximations.ChosenIsometryHomotopies

/-!
# The adjoint homotopy

For `g ∈ G_i`, `a = a_g`, `a' = a_{-g}` and `S = B_{-g,g}`, let `K` be the map of degree `+1` of
`D_i^{N-*}` given by `(-1)^r S^*` in degree `r`, and `V_g = aφ_iK + U_g a'^*`.

## Encoding

`V_g` is a map of degree `+1` from `D_i^{N-*}` to `D_i`, i.e. an element of `M(D_i)_{N+1}`
(`adjointHomotopy`, the declaration of the article): its component from
`(D_i^{N-*})_{N-q} = (D_i)_q^*` to `(D_i)_p`, `p + q = N + 1`, is
`(-1)^{N-q} (S_{q-1})^* ≫ φ_i ≫ (a_g)_p + (a_{-g})_q^* ≫ U_g`, with the chosen `productHomotopy`
and `isometryHomotopy`.
-/

open CategoryTheory

namespace HSP.ChainModels

open FreeQ DualCat

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The *adjoint homotopy* `V_g = a_g φ_i K + U_g a_{-g}^* ∈ M(D_i)_{N+1}`, `K = (-1)^r S^*` in
degree `r` of `D_i^{N-*}`, `S = B_{-g,g}`. -/
noncomputable def adjointHomotopy (A : LocalDatum p n D ρplus) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ' : ρ < ρplus) (i : ℕ) (g : ZMod (p ^ i)) :
    (StructureCx (chainModel A i)).X (((n + 4 : ℕ) : ℤ) + 1) := fun x =>
  (((n + 4 : ℕ) : ℤ) - x.1.2).negOnePow •
      (eqToHom (congrArg (fun t => dual ((chainModel A i).X t))
          (show x.1.2 = x.1.2 - 1 + 1 by ring)) ≫
        dualHom (productHomotopy A hρ hρ' i (-g) g (x.1.2 - 1)) ≫
        (chainModelDuality A i).φ
          ⟨(x.1.1, x.1.2 - 1), by have := x.2; push_cast at this ⊢; omega⟩ ≫
        groupApprox A i g x.1.1) +
    dualHom (groupApprox A i (-g) x.1.2) ≫ isometryHomotopy A i g x

end HSP.ChainModels
