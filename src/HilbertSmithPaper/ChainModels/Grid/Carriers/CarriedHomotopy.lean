import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Carriers.CarriedMap
import HilbertSmithPaper.ChainModels.Grid.Carriers.CarriedChainMap
import HilbertSmithPaper.ChainModels.Grid.BasedSubcomplex

/-!
# Carried homotopies

Chain maps `u, v : E → F` carried by `Γ` that agree on a based subcomplex `E'`, with
`ε u = ε v` on `E₀`, are joined by a carried `H` of degree `+1` with `u - v = dH + Hd` and
`H|_{E'} = 0`; under the label hypothesis of carried chain maps, `prop(H) ≤ a`.

## Encoding

* `H` is a Mathlib `Homotopy u v`: its component `H.hom r (r + 1) : E_r → F_{r+1}` is the
  degree-`+1` map, and `Homotopy.comm` is `u - v = dH + Hd`.
* The based subcomplex `E'` is given by basis sets `S` with `IsBasedSubcomplex`; agreement and
  `H|_{E'} = 0` are checked on its basis elements.
* The propagation clause is that of `exists_carried_chainMap`, for the matrix of
  `H.hom r (r + 1)` in the bases `b r` and `bF (r + 1)`.
-/

open CategoryTheory

namespace HSP.ChainModels

/-- **Carried homotopies.** Carried chain maps `u, v : E → F` that agree on a based subcomplex
`E'`, with `ε u = ε v`, are joined by a carried homotopy `H` (`u - v = dH + Hd`) vanishing on
`E'`; if every label of `Γ(e)` is within `a` of the label of `e`, then `prop(H) ≤ a`. -/
theorem carried_homotopy {E : ChainComplex (ModuleCat.{0} ℚ) ℤ} {ι : ℤ → Type}
    {b : ∀ r, Module.Basis (ι r) ℚ (E.X r)} {F : ChainComplex (ModuleCat.{0} ℚ) ℤ}
    {ε : F.X 0 →ₗ[ℚ] ℚ} (Γ : Carrier E b F ε) (u v : E ⟶ F)
    (hu : Γ.IsCarried (σ := fun r => r) (fun r => u.f r))
    (hv : Γ.IsCarried (σ := fun r => r) (fun r => v.f r))
    (S : ∀ r, Set (ι r)) (hS : IsBasedSubcomplex b S)
    (huv : ∀ r, ∀ e ∈ S r, (u.f r).hom (b r e) = (v.f r).hom (b r e))
    (hε : ε ∘ₗ (u.f 0).hom = ε ∘ₗ (v.f 0).hom) :
    ∃ H : Homotopy u v, Γ.IsCarried (σ := fun r => r + 1) (fun r => H.hom r (r + 1)) ∧
      (∀ r, ∀ e ∈ S r, (H.hom r (r + 1)).hom (b r e) = 0) ∧
      ∀ {X : Type} [MetricSpace X] {κ : ℤ → Type} [∀ s, Fintype (κ s)] [∀ r, Fintype (ι r)]
        (bF : ∀ s, Module.Basis (κ s) ℚ (F.X s)) (lE : ∀ r, ι r → X) (lF : ∀ s, κ s → X)
        (a : ℝ), 0 ≤ a →
        (∀ r (e : ι r) s, ∀ x ∈ Γ.sub r e s, ∀ f, (bF s).repr x f ≠ 0 →
          dist (lF s f) (lE r e) ≤ a) →
        ∀ r, (prop (lE r) (lF (r + 1))
          (Matrix.of fun f e => (bF (r + 1)).repr ((H.hom r (r + 1)).hom (b r e)) f) : ℝ) ≤ a := by
  sorry

end HSP.ChainModels
