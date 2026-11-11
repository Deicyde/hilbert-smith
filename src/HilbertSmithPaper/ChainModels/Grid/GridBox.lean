import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Cubical.GridCube

/-!
# Grid boxes

A grid arc of `S_k` is the subcomplex spanned by `[w], …, [w+m]` and `e_w, …, e_{w+m-1}`
(indices mod `k`), `0 ≤ m ≤ max (k - 2) 0`, with realization the arc from `4w/k` to `4(w+m)/k`. A grid
box is a tensor product `B = A_1 ⊗ ⋯ ⊗ A_n ⊆ C(k)` of grid arcs, spanned by the cubes whose
factors are cells of the arcs, with realization `|B| = ∏_j |A_j|`.

## Encoding

`GridArc k` records the start `w : Fin k` and the length `m ≤ k - 2`; `GridArc.cells` is its set
of cells of `S_k`. `GridBox k n` (the declaration of the article) is a family of grid arcs, one per
coordinate; `GridBox.cubes` is the set of cubes spanning it, `GridBox.realization` its
realization in `𝕋ⁿ`.
-/

namespace HSP.ChainModels

/-- A *grid arc* of `S_k`: start `[w]` and length `m`, with `0 ≤ m ≤ k - 2` in `ℕ`, that is
`0 ≤ m ≤ max (k - 2) 0`. -/
structure GridArc (k : ℕ) where
  /-- The start vertex `[w]`. -/
  start : Fin k
  /-- The number `m` of edges. -/
  length : ℕ
  length_le : length ≤ k - 2

/-- The `j`-th vertex index `w + j` (mod `k`) of a grid arc. -/
def GridArc.vertex {k : ℕ} (A : GridArc k) (j : ℕ) : Fin k :=
  ⟨((A.start : ℕ) + j) % k, Nat.mod_lt _ (Fin.pos A.start)⟩

/-- The cells of a grid arc: `[w], …, [w+m]` and `e_w, …, e_{w+m-1}`. -/
def GridArc.cells {k : ℕ} (A : GridArc k) : Set (Fin k × Bool) :=
  {b | ∃ j, (b.2 = false ∧ j ≤ A.length ∧ b.1 = A.vertex j) ∨
    (b.2 = true ∧ j < A.length ∧ b.1 = A.vertex j)}

/-- The realization `|A|` of a grid arc: the arc from `4w/k` to `4(w+m)/k`. -/
def GridArc.realization {k : ℕ} (A : GridArc k) : Set (AddCircle (4 : ℝ)) :=
  (fun t : ℝ => (t : AddCircle (4 : ℝ))) ''
    Set.Icc (4 * (A.start : ℕ) / k : ℝ) (4 * ((A.start : ℕ) + A.length) / k)

/-- A *grid box* `B = A_1 ⊗ ⋯ ⊗ A_n ⊆ C(k)`: one grid arc for each coordinate. -/
abbrev GridBox (k n : ℕ) : Type := Fin n → GridArc k

/-- The cubes spanning a grid box: those whose `j`-th factor is a cell of `A_j` for every `j`. -/
def GridBox.cubes {k n : ℕ} (B : GridBox k n) : Set (GridCube k n) :=
  {c | ∀ j, c j ∈ (B j).cells}

/-- The realization `|B| = ∏_j |A_j|` of a grid box. -/
def GridBox.realization {k n : ℕ} (B : GridBox k n) : Set (Torus n) :=
  Set.pi Set.univ fun j => (B j).realization

end HSP.ChainModels
