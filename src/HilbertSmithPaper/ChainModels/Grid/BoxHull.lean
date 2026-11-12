import Mathlib
import HilbertSmithPaper.ChainModels.Grid.GridBox
import HilbertSmithPaper.ChainModels.Grid.Cubical.GridCube
import HilbertSmithPaper.ChainModels.Grid.CircleArcs

/-!
# Box hull

For `k ≥ 8` and `X ⊆ 𝕋ⁿ`, let `J_j` be a shortest closed arc containing the coordinate projection
`X_j`, and `A_j` a smallest grid arc with `J_j ⊆ |A_j|`; then `Box_k(X) = ⨂_j A_j`.

## Encoding

* Closed arcs `circleArc a ℓ` and the shortest arc `shortestArc Y` are in
  `ChainModels.Grid.CircleArcs` (the shortest arc is unique under the hypotheses of the
  article's remark; the whole-circle fallback never happens for the sets of the paper).
* `smallestGridArc k hk J` is a grid arc of least length whose realization contains `J` (a
  choice); if none exists it is the one-vertex arc at `[0]`, which uses `k ≥ 8 > 0`.
* `boxHull k hk X` (the declaration of the article) applies these to each coordinate projection.
-/

namespace HSP.ChainModels

open Classical in
/-- A smallest grid arc `A` of `S_k` with `J ⊆ |A|`. -/
noncomputable def smallestGridArc (k : ℕ) (hk : 8 ≤ k) (J : Set (AddCircle (4 : ℝ))) :
    GridArc k :=
  if h : ∃ A : GridArc k, J ⊆ A.realization then
    (Nat.find_spec (⟨_, h.choose, rfl, h.choose_spec⟩ :
      ∃ m, ∃ A : GridArc k, A.length = m ∧ J ⊆ A.realization)).choose
  else ⟨⟨0, by omega⟩, 0, Nat.zero_le _⟩

/-- The *box hull* `Box_k(X) = ⨂_j A_j`, `A_j` the smallest grid arc containing the shortest
closed arc `J_j` that contains the coordinate projection `X_j`. -/
noncomputable def boxHull (k : ℕ) (hk : 8 ≤ k) {n : ℕ} (X : Set (Torus n)) : GridBox k n :=
  fun j => smallestGridArc k hk (shortestArc ((fun x : Torus n => x j) '' X))

end HSP.ChainModels
