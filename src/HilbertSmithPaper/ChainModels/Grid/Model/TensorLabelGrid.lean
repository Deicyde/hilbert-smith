import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Model.TensorLabel
import HilbertSmithPaper.ChainModels.Grid.Model.ChainModelLabel
import HilbertSmithPaper.ChainModels.Grid.Cubical.GridCell
import HilbertSmithPaper.ChainModels.Grid.Cubical.GridCube
import HilbertSmithPaper.ChainModels.Grid.CircleDuality

/-!
# Grid and chain-model labels are tensor labels

The center labels of `C(k) ⊗ S_k` are the tensor labels of the center labels of `C(k)` and of
`S_k`, combined by appending a coordinate, a map that is `1`-Lipschitz for the max distance; the
torus labels of `D_i = C(k_i) ⊗ P` are the tensor labels of the center labels of `C(k_i)`,
forgetting the `CP²` factor.

## Encoding

`tensorLabel_grid` (the declaration of the article) is the conjunction of the three statements,
with the center labels of `C(k)` written `fun r a => (gridCell k n r a).center`.
-/

namespace HSP.ChainModels

open FreeQ

/-- *Grid and chain-model labels are tensor labels.* Appending a coordinate is `1`-Lipschitz for the
max distance; the center labels of `C(k) ⊗ S_k` are the tensor labels of those of `C(k)` and `S_k`
combined by appending; the torus labels of `D_i` are the tensor labels of the center labels of
`C(k_i)`, forgetting `P`. -/
theorem tensorLabel_grid :
    (∀ (n : ℕ) (x y : Torus n) (a b : AddCircle (4 : ℝ)),
      nndist (Fin.snoc x a : Torus (n + 1)) (Fin.snoc y b) ≤ max (nndist x y) (nndist a b)) ∧
    (∀ (k n : ℕ) (r : ℤ), (fun a => (gridCell k (n + 1) r a).center) =
      tensorLabel (circleComplex_dim_neg k) (fun r a => (gridCell k n r a).center) (circleLabel k)
        (fun x a => (Fin.snoc x a : Torus (n + 1))) r) ∧
    (∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (D ρplus : ℝ) (A : LocalDatum p n D ρplus) (i : ℕ) (r : ℤ),
      chainModelLabel A i r = tensorLabel cp2Complex_dim_neg
        (fun r a => (gridCell (meshSequence A i) n r a).center) (fun _ _ => (0 : ℝ))
        (fun x _ => x) r) := by
  refine ⟨fun n x y a b => ?_, fun k n r => ?_, fun p _ n D ρplus A i r => ?_⟩
  · refine (nndist_pi_le_iff).2 fun j => ?_
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [Fin.snoc_last]
      exact le_max_right _ _
    · simp only [Fin.snoc_castSucc]
      exact (nndist_le_pi_nndist x y j).trans (le_max_left _ _)
  · funext a
    refine funext fun j => Fin.lastCases ?_ (fun j => ?_) j
    · simp only [gridCell, tensorLabel, GridCube.center, Fin.snoc_last, circleLabel]
    · simp only [gridCell, tensorLabel, GridCube.center, Fin.snoc_castSucc]
  · funext a
    rfl

end HSP.ChainModels
