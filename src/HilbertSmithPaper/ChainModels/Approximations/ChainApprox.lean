import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Carriers.CarriedMap
import HilbertSmithPaper.ChainModels.Grid.RealizedAugmentation
import HilbertSmithPaper.ChainModels.Approximations.FarCubes
import HilbertSmithPaper.ChainModels.Approximations.ChainApproxBox
import HilbertSmithPaper.ChainModels.Approximations.ChainApproxExists
import HilbertSmithPaper.ChainModels.Approximations.Maps.TrackFamily
import HilbertSmithPaper.ChainModels.Grid.Cubical.GridAug
import HilbertSmithPaper.ChainModels.Grid.Cubical.GridCell
import HilbertSmithPaper.ChainModels.Grid.Cubical.CubicalTorusGrid
import HilbertSmithPaper.ChainModels.Mesh.MeshStart

/-!
# Chain approximation

`a_i[L]` is a chain map chosen by "chain approximations exist" for `k = k_i`.

## Encoding

`chainApprox A i hL` (the declaration of the article) is the chain map `a` of
`C(k_i) = gridComplex (meshSequence A i) n` chosen (`Exists.choose`) from `exists_chainApprox`
with `k = k_i ≥ k₀`, for `L ∈ 𝓕` (`hL : L ∈ trackFamily A`). `chainApprox_spec` records its
properties.
-/

open CategoryTheory

namespace HSP.ChainModels

open FreeQ

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- `k_i ≥ k₀`. -/
private lemma meshStart_le_meshSequence (A : LocalDatum p n D ρplus) (i : ℕ) :
    meshStart A ≤ meshSequence A i :=
  Nat.le_add_right _ _

/-- The *chain approximation* `a_i[L]`: a chain map of `C(k_i)` chosen by "chain approximations
exist" for `k = k_i`. -/
noncomputable def chainApprox (A : LocalDatum p n D ρplus) (i : ℕ) {L : Torus n → Torus n}
    (hL : L ∈ trackFamily A) :
    gridComplex (meshSequence A i) n ⟶ gridComplex (meshSequence A i) n :=
  (exists_chainApprox A (meshStart_le_meshSequence A i) hL).choose_spec.2.2.choose

/-- The properties of `a_i[L]`: carried by `Γ_L` (for the chosen carrier with subcomplexes
`Γ_L(c)`), the identity on `E(k_i)`, and `ε a_i[L] = ε`. -/
private lemma chainApprox_spec (A : LocalDatum p n D ρplus) (i : ℕ) {L : Torus n → Torus n}
    (hL : L ∈ trackFamily A) :
    let Γ := (exists_chainApprox A (meshStart_le_meshSequence A i) hL).choose
    (∀ r e s, Γ.sub r e s = cubeSpan (chainApproxBox A (meshStart_le_meshSequence A i) L r e).cubes
      s) ∧
    Γ.IsCarried (σ := fun r => r) (fun r => realization.map ((chainApprox A i hL).f r)) ∧
    (∀ r (e : Fin ((gridComplex (meshSequence A i) n).X r).dim),
      IsFarCube (gridCell (meshSequence A i) n r e) →
        (fun e' => toMatrix ((chainApprox A i hL).f r) e' e) = Pi.single e 1) ∧
    (chainApprox A i hL).f 0 ≫ gridAug (meshSequence A i) n = gridAug (meshSequence A i) n := by
  have h := (exists_chainApprox A (meshStart_le_meshSequence A i) hL).choose_spec
  exact ⟨h.1, h.2.2.choose_spec⟩

end HSP.ChainModels
