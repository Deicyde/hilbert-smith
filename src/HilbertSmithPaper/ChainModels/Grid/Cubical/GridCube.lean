import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Cubical.CircleComplex

/-!
# Grid cubes

A cube `c = b_1 ⊗ ⋯ ⊗ b_n` of the cubical torus grid is a choice of a cell `b_j = (w_j, j ∈ S)` of
`S_k` for each coordinate. Its dimension is `|S|`, its closed cube `|c| ⊆ 𝕋ⁿ` is the product of the
realizations of its cells, its center `x_c` has coordinates `4w_j/k`, plus `2/k` in the edge
coordinates, its closed star is the union of the closed cubes containing `|c|`, and its faces in an
edge coordinate `j` replace `e_{w_j}` by `[w_j]` and `[w_j + 1]`. A set of cubes closed under faces
is a subcomplex.

## Encoding

`GridCube k n` (the declaration of the article) is `Fin n → Fin k × Bool`; `GridCube.dim`,
`GridCube.realization`, `GridCube.center`, `GridCube.closedStar`, `GridCube.face` and
`IsGridSubcomplex` are its companions.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.ChainModels

open FreeQ

/-- A *cube* `c = (w, S)` of the grid: for each coordinate `j` the cell `b_j = (w_j, j ∈ S)` of
`S_k`. -/
abbrev GridCube (k n : ℕ) : Type := Fin n → Fin k × Bool

/-- The dimension `|S|` of a cube: the number of its edge coordinates. -/
def GridCube.dim {k n : ℕ} (c : GridCube k n) : ℕ :=
  ∑ j, if (c j).2 then 1 else 0

/-- The closed cube `|c| ⊆ 𝕋ⁿ`, the product of the realizations of its cells. -/
def GridCube.realization {k n : ℕ} (c : GridCube k n) : Set (Torus n) :=
  Set.pi Set.univ fun j => cellRealization k (c j)

/-- The center `x_c` of a cube: `4w_j/k`, plus `2/k` in the edge coordinates. -/
noncomputable def GridCube.center {k n : ℕ} (c : GridCube k n) : Torus n :=
  fun j => ((4 * ((c j).1 : ℕ) + if (c j).2 then 2 else 0) / k : ℝ)

/-- The closed star `st(c)`: the union of the closed cubes containing `|c|`. -/
def GridCube.closedStar {k n : ℕ} (c : GridCube k n) : Set (Torus n) :=
  ⋃ (c' : GridCube k n) (_ : c.realization ⊆ c'.realization), c'.realization

/-- The two faces of a cube in an edge coordinate `j`: `[w_j]` and `[w_j + 1]` replace `e_{w_j}`. -/
def GridCube.face {k n : ℕ} (c : GridCube k n) (j : Fin n) (top : Bool) : GridCube k n :=
  Function.update c j
    (if top then ⟨((c j).1 + 1 : ℕ) % k, Nat.mod_lt _ (Fin.pos (c j).1)⟩ else (c j).1, false)

/-- A *subcomplex*: a set of cubes closed under taking faces (its span is the subcomplex). -/
def IsGridSubcomplex {k n : ℕ} (s : Set (GridCube k n)) : Prop :=
  ∀ c ∈ s, ∀ j, (c j).2 = true → ∀ top, c.face j top ∈ s

end HSP.ChainModels
