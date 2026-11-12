import Mathlib
import HilbertSmithPaper.ChainModels.Grid.AcyclicCarriers
import HilbertSmithPaper.ChainModels.Grid.BasedSubcomplex
import HilbertSmithPaper.Categories.Asymptotic.Propagation

/-!
# Carried chain maps

Let `Γ` be a carrier from `E` to `F`, and `ε_E : E₀ → ℚ` with `ε_E d₁ = 0`. A carried chain map
`u' : E' → F` on a based subcomplex `E' ⊆ E` with `ε u' = ε_E` on `E'₀` extends to a carried
chain map `u : E → F` with `ε u = ε_E`. If every label of `Γ(e)` is within `a` of the label of
`e`, then `prop(u) ≤ a`.

## Encoding

* A based subcomplex `E' ⊆ E` is a set `S r` of basis elements in each degree whose span is
  closed under `d` (`IsBasedSubcomplex`, based subcomplexes).
* The chain map `u' : E' → F` is given by a graded linear map `u' r : E_r → F_r` constrained on
  the basis elements of `E'` only (a linear map on `E'` is its values on these): `d u'(e) =
  u'(de)`, `u'(e) ∈ Γ(e)` and `ε u'(e) = ε_E(e)` for `e ∈ E'`. The extension `u` agrees with
  `u'` on these basis elements, which is `u|_{E'} = u'`.
* The propagation clause takes a basis `bF` of `F` with finitely many elements in each degree
  and labels `lE`, `lF` in a metric space. "Every label of `Γ(e)` is within `a` of the label of
  `e`" says that every basis element of `F` occurring in an element of `Γ(e)` has label within
  `a` of that of `e`; `prop(u_r)` is the propagation of the matrix of `u_r` in the bases `b`,
  `bF`. The clause holds for every such choice of bases and labels, as the article's `u` does not
  depend on them.
-/

open CategoryTheory

namespace HSP.ChainModels

/-- **Carried chain maps.** A carried chain map on a based subcomplex `E' ⊆ E`, compatible with
the augmentations, extends to a carried chain map `u : E → F` with `ε u = ε_E`; if every label
of `Γ(e)` is within `a` of the label of `e`, then `prop(u) ≤ a`. -/
theorem exists_carried_chainMap {E : ChainComplex (ModuleCat.{0} ℚ) ℤ} {ι : ℤ → Type}
    {b : ∀ r, Module.Basis (ι r) ℚ (E.X r)} {F : ChainComplex (ModuleCat.{0} ℚ) ℤ}
    {ε : F.X 0 →ₗ[ℚ] ℚ} (Γ : Carrier E b F ε)
    (εE : E.X 0 →ₗ[ℚ] ℚ) (hεE : εE ∘ₗ (E.d 1 0).hom = 0)
    (S : ∀ r, Set (ι r)) (hS : IsBasedSubcomplex b S) (u' : ∀ r, E.X r ⟶ F.X r)
    (hu'd : ∀ r, ∀ e ∈ S r, (F.d r (r - 1)).hom ((u' r).hom (b r e)) =
      (u' (r - 1)).hom ((E.d r (r - 1)).hom (b r e)))
    (hu'Γ : ∀ r, ∀ e ∈ S r, (u' r).hom (b r e) ∈ Γ.sub r e r)
    (hu'ε : ∀ e ∈ S 0, ε ((u' 0).hom (b 0 e)) = εE (b 0 e)) :
    ∃ u : E ⟶ F, Γ.IsCarried (σ := fun r => r) (fun r => u.f r) ∧
      (∀ r, ∀ e ∈ S r, (u.f r).hom (b r e) = (u' r).hom (b r e)) ∧
      ε ∘ₗ (u.f 0).hom = εE ∧
      ∀ {X : Type} [MetricSpace X] {κ : ℤ → Type} [∀ s, Fintype (κ s)] [∀ r, Fintype (ι r)]
        (bF : ∀ s, Module.Basis (κ s) ℚ (F.X s)) (lE : ∀ r, ι r → X) (lF : ∀ s, κ s → X)
        (a : ℝ), 0 ≤ a →
        (∀ r (e : ι r) s, ∀ x ∈ Γ.sub r e s, ∀ f, (bF s).repr x f ≠ 0 →
          dist (lF s f) (lE r e) ≤ a) →
        ∀ r, (prop (lE r) (lF r) (Matrix.of fun f e => (bF r).repr ((u.f r).hom (b r e)) f) :
          ℝ) ≤ a := by
  sorry

end HSP.ChainModels
