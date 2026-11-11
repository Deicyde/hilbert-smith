import Mathlib
import HilbertSmithPaper.LocalData.Control.FixedLocalData
import HilbertSmithPaper.ChainModels.Approximations.TorusTestMap
import HilbertSmithPaper.ChainModels.Grid.ChainModel
import HilbertSmithPaper.ChainModels.Grid.Cubical.GridCube

/-!
# Retained and discarded cells

For fixed local data with buffer radius `t` and torus test map `f_T` (of the pinch radius `ρ`),
`K_t = f_T⁻¹(B̄(0, t)) ⊆ 𝕋ⁿ`. A cell `c ⊗ e_r` of the chain model `D_i`, and its dual in
`D_i^{N-*}`, is retained if the closed cube `|c|` meets `K_t`, and discarded otherwise; `Ret_i` is
the set of retained cells of `D_i`.

## Encoding

* `testPreimage F` is `K_t`, the preimage under `f_T` of the image of the closed Euclidean ball
  `B̄(0, t) ⊆ ℝⁿ` in `Sⁿ`.
* `IsRetained F i r a` (the declaration of the article) says that the closed cube of the basis
  cell `a` of `(D_i)_r` meets `K_t`; a cell is discarded when this fails.
* `retainedCells F i r` is `Ret_i` in degree `r`, a finset of basis indices of `(D_i)_r` (the
  filter uses classical decidability). The dual cell `a^*` of `(D_i^{N-*})_r = ((D_i)_{N-r})^*`
  carries the index `a` of `(D_i)_{N-r}`, and is retained exactly when `a` is
  (`IsRetainedDual`, `retainedDualCells`), `N = n + 4`.
-/

namespace HSP.Compression

open HSP.ChainModels

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The set `K_t = f_T⁻¹(B̄(0, t)) ⊆ 𝕋ⁿ`, for the torus test map `f_T` of the pinch radius `ρ`
and the buffer radius `t`. -/
def testPreimage (F : FixedLocalData p n D ρplus) : Set (Torus n) :=
  torusTestMap F.toLocalDatum F.ρ ⁻¹'
    ((↑) '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) F.t)

/-- The basis cell `a = c ⊗ e` of `(D_i)_r` is *retained* if its closed cube `|c|` meets
`K_t`; it is *discarded* otherwise. -/
def IsRetained (F : FixedLocalData p n D ρplus) (i : ℕ) (r : ℤ)
    (a : Fin ((chainModel F.toLocalDatum i).X r).dim) : Prop :=
  ((chainModelCube F.toLocalDatum i r a).realization ∩ testPreimage F).Nonempty

/-- The dual cell `a^*` of `(D_i^{N-*})_r = ((D_i)_{N-r})^*` is retained if `a` is. -/
def IsRetainedDual (F : FixedLocalData p n D ρplus) (i : ℕ) (r : ℤ)
    (a : Fin ((chainModel F.toLocalDatum i).X ((n + 4 : ℕ) - r)).dim) : Prop :=
  IsRetained F i ((n + 4 : ℕ) - r) a

open Classical in
/-- `Ret_i` in degree `r`: the retained basis cells of `(D_i)_r`. -/
noncomputable def retainedCells (F : FixedLocalData p n D ρplus) (i : ℕ) (r : ℤ) :
    Finset (Fin ((chainModel F.toLocalDatum i).X r).dim) :=
  Finset.univ.filter (IsRetained F i r)

/-- The retained dual cells of `(D_i^{N-*})_r`. -/
noncomputable def retainedDualCells (F : FixedLocalData p n D ρplus) (i : ℕ) (r : ℤ) :
    Finset (Fin ((chainModel F.toLocalDatum i).X ((n + 4 : ℕ) - r)).dim) :=
  retainedCells F i ((n + 4 : ℕ) - r)

lemma mem_retainedCells (F : FixedLocalData p n D ρplus) (i : ℕ) (r : ℤ)
    (a : Fin ((chainModel F.toLocalDatum i).X r).dim) :
    a ∈ retainedCells F i r ↔ IsRetained F i r a := by
  classical
  simp [retainedCells]

end HSP.Compression
