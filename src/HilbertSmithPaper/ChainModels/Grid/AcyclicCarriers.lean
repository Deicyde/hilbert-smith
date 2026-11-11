import Mathlib

/-!
# Carriers

A *carrier* from a finite based chain complex `E` in degrees `≥ 0` to a rational chain complex
`F` with augmentation `ε` assigns to every basis element `e` of `E` an augmented acyclic
subcomplex `Γ(e) ⊆ F`, nested under the faces of `e`. A graded linear map `E → F` is *carried*
when it sends every basis element `e` into `Γ(e)`.

## Encoding

* Rational chain complexes are `ChainComplex (ModuleCat ℚ) ℤ`; `F.d s (s - 1)` is the
  differential out of degree `s`.
* The basis of `E` is a family `b r : Module.Basis (ι r) ℚ (E.X r)`; *finite* means finitely
  many basis elements in all, and *in degrees `≥ 0`* means no basis elements in negative degrees.
* The augmentation is a linear map `ε : F₀ → ℚ` with `ε ∘ d₁ = 0`.
* A subcomplex `Γ(e)` is a family of submodules `Γ(e)_s ⊆ F_s` closed under `d`. It is
  *augmented acyclic* when `H_s(Γ(e)) = 0` for `s > 0` and `ε` induces `H₀(Γ(e)) ≅ ℚ`; this is
  spelled out on elements: every cycle of positive degree bounds in `Γ(e)`, every degree-0 cycle
  with augmentation `0` bounds in `Γ(e)`, and some degree-0 cycle has augmentation `1`.
* `e'` *occurs in* `de` when the `e'`-coordinate of `de` is nonzero.
* A linear map of any degree is a family `u r : E_r → F_{σ r}`; a map of degree `m` has
  `σ r = r + m`. Taking `σ` arbitrary lets a chain map (`σ = id`) and a homotopy
  (`σ r = r + 1`) be passed directly.
-/

open CategoryTheory

namespace HSP.ChainModels

/-- A *carrier* `Γ` from the based complex `E` (basis `b`) to the rational complex `F` with
augmentation `ε`: for every basis element `e` of `E` (of degree `r`) an augmented acyclic
subcomplex `Γ(e) ⊆ F`, with `Γ(e') ⊆ Γ(e)` whenever `e'` occurs in `de`. The fields
`finite`, `degrees_nonneg` and `augmentation` record the standing hypotheses on `E` and `ε`. -/
structure Carrier (E : ChainComplex (ModuleCat.{0} ℚ) ℤ) {ι : ℤ → Type}
    (b : ∀ r, Module.Basis (ι r) ℚ (E.X r)) (F : ChainComplex (ModuleCat.{0} ℚ) ℤ)
    (ε : F.X 0 →ₗ[ℚ] ℚ) where
  /-- `E` is finite: finitely many basis elements in all. -/
  finite : Finite (Σ r, ι r)
  /-- `E` lives in degrees `≥ 0`. -/
  degrees_nonneg : ∀ r < 0, IsEmpty (ι r)
  /-- `ε` is an augmentation: `ε ∘ d₁ = 0`. -/
  augmentation : ε ∘ₗ (F.d 1 0).hom = 0
  /-- The degree-`s` part `Γ(e)_s ⊆ F_s` of the subcomplex assigned to the basis element `e`. -/
  sub : ∀ r, ι r → ∀ s, Submodule ℚ (F.X s)
  /-- `Γ(e)` is a subcomplex: closed under the differential. -/
  d_mem : ∀ r (e : ι r) s, ∀ x ∈ sub r e s, (F.d s (s - 1)).hom x ∈ sub r e (s - 1)
  /-- Acyclicity in positive degrees: `H_s(Γ(e)) = 0` for `s > 0`. -/
  exact_pos : ∀ r (e : ι r) s, 0 < s → ∀ z ∈ sub r e s, (F.d s (s - 1)).hom z = 0 →
    ∃ y ∈ sub r e (s + 1), (F.d (s + 1) s).hom y = z
  /-- `ε` is injective on `H₀(Γ(e))`: a degree-0 cycle with augmentation `0` bounds. -/
  exact_zero : ∀ r (e : ι r), ∀ z ∈ sub r e 0, (F.d 0 (-1)).hom z = 0 → ε z = 0 →
    ∃ y ∈ sub r e 1, (F.d 1 0).hom y = z
  /-- `ε` is onto on `H₀(Γ(e))`: some degree-0 cycle has augmentation `1`. -/
  aug_onto : ∀ r (e : ι r), ∃ z ∈ sub r e 0, (F.d 0 (-1)).hom z = 0 ∧ ε z = 1
  /-- Nesting: `Γ(e') ⊆ Γ(e)` whenever `e'` occurs in `de`. -/
  nested : ∀ r (e : ι r) (e' : ι (r - 1)),
    (b (r - 1)).repr ((E.d r (r - 1)).hom (b r e)) e' ≠ 0 → ∀ s, sub (r - 1) e' s ≤ sub r e s

namespace Carrier

variable {E : ChainComplex (ModuleCat.{0} ℚ) ℤ} {ι : ℤ → Type}
  {b : ∀ r, Module.Basis (ι r) ℚ (E.X r)} {F : ChainComplex (ModuleCat.{0} ℚ) ℤ} {ε : F.X 0 →ₗ[ℚ] ℚ}

/-- A linear map `u` from `E` to `F`, sending `E_r` to `F_{σ r}` (of degree `m` when
`σ r = r + m`), is *carried* by `Γ` if `u(e) ∈ Γ(e)` for every basis element `e`. -/
def IsCarried (Γ : Carrier E b F ε) {σ : ℤ → ℤ} (u : ∀ r, E.X r ⟶ F.X (σ r)) : Prop :=
  ∀ r (e : ι r), (u r).hom (b r e) ∈ Γ.sub r e (σ r)

end Carrier

end HSP.ChainModels
