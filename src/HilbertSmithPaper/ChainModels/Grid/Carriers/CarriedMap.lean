import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Carriers.AcyclicCarriers

/-!
# Carried maps

A graded linear map `u` from a based complex `E` to `F`, sending `E_r` to `F_{σ r}`, is
*carried* by a carrier `Γ` when it sends every basis element `e` into `Γ(e)`. Taking `σ`
arbitrary lets a chain map (`σ = id`) and a homotopy (`σ r = r + 1`) be passed directly.
-/

open CategoryTheory

namespace HSP.ChainModels

namespace Carrier

variable {E : ChainComplex (ModuleCat.{0} ℚ) ℤ} {ι : ℤ → Type}
  {b : ∀ r, Module.Basis (ι r) ℚ (E.X r)} {F : ChainComplex (ModuleCat.{0} ℚ) ℤ} {ε : F.X 0 →ₗ[ℚ] ℚ}

/-- A linear map `u` from `E` to `F`, sending `E_r` to `F_{σ r}` (of degree `m` when
`σ r = r + m`), is *carried* by `Γ` if `u(e) ∈ Γ(e)` for every basis element `e`. -/
def IsCarried (Γ : Carrier E b F ε) {σ : ℤ → ℤ} (u : ∀ r, E.X r ⟶ F.X (σ r)) : Prop :=
  ∀ r (e : ι r), (u r).hom (b r e) ∈ Γ.sub r e (σ r)

end Carrier

end HSP.ChainModels
