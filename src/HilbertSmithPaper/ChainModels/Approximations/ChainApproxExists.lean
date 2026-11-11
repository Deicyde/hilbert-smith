import Mathlib
import HilbertSmithPaper.ChainModels.Grid.GridBoxAcyclic
import HilbertSmithPaper.ChainModels.Grid.AcyclicCarriers
import HilbertSmithPaper.ChainModels.Grid.RealizedAugmentation
import HilbertSmithPaper.ChainModels.Approximations.FarCubes
import HilbertSmithPaper.ChainModels.Approximations.ChainApproxBox
import HilbertSmithPaper.ChainModels.Approximations.TrackMap
import HilbertSmithPaper.ChainModels.Approximations.Modulus
import HilbertSmithPaper.ChainModels.Approximations.Maps.TrackFamily
import HilbertSmithPaper.ChainModels.Grid.Cubical.GridAug
import HilbertSmithPaper.ChainModels.Grid.Cubical.GridCell
import HilbertSmithPaper.ChainModels.Grid.Cubical.CubicalTorusGrid
import HilbertSmithPaper.ChainModels.Grid.Cubical.GridCube

/-!
# Chain approximations exist

`E(k) ⊆ C(k)` is spanned by the cubes whose closed cubes miss `B̄(0, 3/2)`. For `k ≥ k₀` and
`L ∈ 𝓕`, `Γ_L(c) = Box_k(N_h(L|c|))` is a carrier of `d_∞`-diameter at most `ω(h) + 4h`, and
some chain map `a : C(k) → C(k)` carried by `Γ_L` has `a|_{E(k)} = 1` and `ε a = ε`.

## Encoding

* `C(k)` is `gridComplex k n`; as a source and target of a carrier it is realized
  (`realizeCx`, with the standard basis `realizeBasis`, indexed by the basis cubes), with the
  realized augmentation `gridAugLin k n`.
* The basis cubes of `E(k)` are the far cubes (`IsFarCube`).
* `Γ_L(c)` is `chainApproxBox A hk L r e` (approximation boxes); its degree-`s` part is `cubeSpan (chainApproxBox …).cubes s`. The `d_∞`-diameter of the carrier is
  that of the realizations `|Γ_L(c)|`.
* `exists_chainApprox` (the declaration of the article): a carrier `Γ` whose subcomplexes are
  the `Γ_L(c)`, the diameter bound, and a chain map `a` of `C(k)` (in based vector spaces) whose
  realization is carried by `Γ`, which fixes every basis cube of `E(k)` and has `a₀ ≫ ε = ε`.
-/

open CategoryTheory

namespace HSP.ChainModels

open FreeQ Matrix

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- **Chain approximations exist.** For `k ≥ k₀` and `L ∈ 𝓕`, `Γ_L(c) = Box_k(N_h(L|c|))` is a
carrier of `d_∞`-diameter at most `ω(h) + 4h`, and there is a chain map `a : C(k) → C(k)`
carried by `Γ_L` with `a|_{E(k)} = 1` and `ε a = ε`. -/
theorem exists_chainApprox (A : LocalDatum p n D ρplus) {k : ℕ} (hk : meshStart A ≤ k)
    {L : Torus n → Torus n} (hL : L ∈ trackFamily A) :
    ∃ Γ : Carrier (realizeCx (gridComplex k n)) (realizeBasis (gridComplex k n))
        (realizeCx (gridComplex k n)) (gridAugLin k n),
      (∀ r e s, Γ.sub r e s = cubeSpan (chainApproxBox A hk L r e).cubes s) ∧
      (∀ r e, Metric.diam (chainApproxBox A hk L r e).realization ≤
        trackModulus A (4 / k) + 4 * (4 / k : ℝ)) ∧
      ∃ a : gridComplex k n ⟶ gridComplex k n,
        Γ.IsCarried (σ := fun r => r) (fun r => realization.map (a.f r)) ∧
        (∀ r (e : Fin ((gridComplex k n).X r).dim), IsFarCube (gridCell k n r e) →
          (fun e' => toMatrix (a.f r) e' e) = Pi.single e 1) ∧
        a.f 0 ≫ gridAug k n = gridAug k n := by
  sorry

end HSP.ChainModels
