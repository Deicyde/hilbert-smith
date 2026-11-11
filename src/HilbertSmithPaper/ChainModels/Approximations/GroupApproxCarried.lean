import Mathlib
import HilbertSmithPaper.ChainModels.Grid.RealizedAugmentation
import HilbertSmithPaper.ChainModels.Approximations.FarCubes
import HilbertSmithPaper.ChainModels.Approximations.ChainApproxBox
import HilbertSmithPaper.ChainModels.Approximations.GroupApprox
import HilbertSmithPaper.ChainModels.Approximations.TensorOneP

/-!
# Carried group approximations

For every `g ∈ G_i`, `a_g = a^T_g ⊗ 1_P` where `a^T_g` is a chain map of `C(k_i)` carried by
`Γ_{\widehat{r_i(g)}}` of "chain approximations exist", with `a^T_g|_{E(k_i)} = 1` and
`ε a^T_g = ε`.

## Encoding

As in `exists_chainApprox`: the carrier is a `Carrier` on the realization of `C(k_i)` whose
subcomplexes are `Γ_L(c) = chainApproxBox …` for `L = \widehat{r_i(g)}` (`completedRep`), and
`a^T_g ⊗ 1_P` is `tensorOneP` in degree `0`, compared with `groupApprox` in every degree.
-/

open CategoryTheory

namespace HSP.ChainModels

open FreeQ

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- **Carried group approximations.** For every `g ∈ G_i`, `a_g = a^T_g ⊗ 1_P` with `a^T_g` a
chain map of `C(k_i)` carried by `Γ_{\widehat{r_i(g)}}`, `a^T_g|_{E(k_i)} = 1` and
`ε a^T_g = ε`. -/
theorem groupApprox_carried (A : LocalDatum p n D ρplus) (i : ℕ) (g : ZMod (p ^ i)) :
    ∃ aT : gridComplex (meshSequence A i) n ⟶ gridComplex (meshSequence A i) n,
      (∀ r, groupApprox A i g r = tensorOneP A i 0 (fun s => aT.f s ≫
        eqToHom (congrArg (gridComplex (meshSequence A i) n).X (add_zero s).symm)) r ≫
          eqToHom (congrArg (chainModel A i).X (add_zero r))) ∧
      ∃ Γ : Carrier (realizeCx (gridComplex (meshSequence A i) n))
          (realizeBasis (gridComplex (meshSequence A i) n))
          (realizeCx (gridComplex (meshSequence A i) n)) (gridAugLin (meshSequence A i) n),
        (∀ r e s, Γ.sub r e s =
          cubeSpan (chainApproxBox A (Nat.le_add_right (meshStart A) i) (completedRep A i g) r e).cubes
            s) ∧
        Γ.IsCarried (σ := fun r => r) (fun r => realization.map (aT.f r)) ∧
        (∀ r (e : Fin ((gridComplex (meshSequence A i) n).X r).dim),
          IsFarCube (gridCell (meshSequence A i) n r e) →
            (fun e' => toMatrix (aT.f r) e' e) = Pi.single e 1) ∧
        aT.f 0 ≫ gridAug (meshSequence A i) n = gridAug (meshSequence A i) n := by
  sorry

end HSP.ChainModels
