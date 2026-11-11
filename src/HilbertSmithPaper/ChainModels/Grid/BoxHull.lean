import Mathlib
import HilbertSmithPaper.ChainModels.Grid.GridBox

/-!
# Box hull

For `k ≥ 8` and `X ⊆ 𝕋ⁿ`, let `J_j` be a shortest closed arc containing the coordinate projection
`X_j`, and `A_j` a smallest grid arc with `J_j ⊆ |A_j|`; then `Box_k(X) = ⨂_j A_j`.

## Encoding

* A closed arc of `ℝ/4ℤ` is `circleArc a ℓ`, the image of `[a, a + ℓ]`, `ℓ ≥ 0`.
* `shortestArc Y` is a closed arc containing `Y` of least length (a choice; it is unique under
  the hypotheses of the article's remark); if no arc of least length exists it is the whole
  circle, which never happens for the sets of the paper.
* `smallestGridArc k hk J` is a grid arc of least length whose realization contains `J` (a
  choice); if none exists it is the one-vertex arc at `[0]`, which uses `k ≥ 8 > 0`.
* `boxHull k hk X` (the declaration of the article) applies these to each coordinate projection.
-/

namespace HSP.ChainModels

/-- The closed arc of `ℝ/4ℤ` from `a` to `a + ℓ`. -/
def circleArc (a ℓ : ℝ) : Set (AddCircle (4 : ℝ)) :=
  (fun t : ℝ => (t : AddCircle (4 : ℝ))) '' Set.Icc a (a + ℓ)

open Classical in
/-- A shortest closed arc `J` containing `Y`. -/
noncomputable def shortestArc (Y : Set (AddCircle (4 : ℝ))) : Set (AddCircle (4 : ℝ)) :=
  if h : ∃ q : ℝ × ℝ, 0 ≤ q.2 ∧ Y ⊆ circleArc q.1 q.2 ∧
      ∀ q' : ℝ × ℝ, 0 ≤ q'.2 → Y ⊆ circleArc q'.1 q'.2 → q.2 ≤ q'.2 then
    circleArc h.choose.1 h.choose.2
  else Set.univ

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
