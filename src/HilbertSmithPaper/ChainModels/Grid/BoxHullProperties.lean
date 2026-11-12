import Mathlib
import HilbertSmithPaper.ChainModels.Grid.BoxHull
import HilbertSmithPaper.ChainModels.Grid.Cubical.GridCube
import HilbertSmithPaper.ChainModels.Grid.Cubical.GridCubeRealization

/-!
# Box hull properties

For `X, Y ⊆ 𝕋ⁿ` satisfying the hypotheses of the box hull, with shortest arcs `J_j` for `X`, and
`h = 4/k`: the hull is monotone, `|Box_k(X)|` lies in the closed `d_∞`-neighbourhood of radius `h`
of `∏_j J_j` (so its diameter is at most `diam X + 2h`), and every cube whose closed cube meets
`X` lies in `Box_k(N_h(X))` when the hull of `N_h(X)` is defined.

## Encoding

* `IsBoxHullAdmissible X` is the hypothesis under which the hull is used (box hull, Remark):
  `X` is nonempty and every coordinate projection `X_j` lies in a closed arc of length at most
  `1`.
* `Box_k(X) ⊆ Box_k(Y)` is containment of the spanning cubes (`GridBox.cubes`); `|·|` is
  `GridBox.realization`; `d_∞` is the metric of `Torus n`; `N_h(X)` is
  `Metric.cthickening h X`; diameters are `Metric.diam`.
-/

namespace HSP.ChainModels

/-- The hypotheses of the box hull: `X` is nonempty and each coordinate projection `X_j` lies in
a closed arc of length at most `1`. -/
def IsBoxHullAdmissible {n : ℕ} (X : Set (Torus n)) : Prop :=
  X.Nonempty ∧ ∀ j : Fin n, ∃ a ℓ : ℝ, 0 ≤ ℓ ∧ ℓ ≤ 1 ∧
    (fun x : Torus n => x j) '' X ⊆ circleArc a ℓ

/-- **Box hull properties.** For admissible `X, Y ⊆ 𝕋ⁿ`, `k ≥ 8` and `h = 4/k`:
1. if `X ⊆ Y` then `Box_k(X) ⊆ Box_k(Y)`;
2. `|Box_k(X)|` lies in the closed `d_∞`-neighbourhood of radius `h` of `∏_j J_j`, and
   `diam_∞ |Box_k(X)| ≤ diam_∞ X + 2h`;
3. if `N_h(X)` is admissible, every cube whose closed cube meets `X` lies in `Box_k(N_h(X))`. -/
theorem boxHull_properties (k : ℕ) (hk : 8 ≤ k) {n : ℕ} (X Y : Set (Torus n))
    (hX : IsBoxHullAdmissible X) (hY : IsBoxHullAdmissible Y) :
    -- (1)
    (X ⊆ Y → (boxHull k hk X).cubes ⊆ (boxHull k hk Y).cubes) ∧
    -- (2)
    ((boxHull k hk X).realization ⊆ Metric.cthickening (4 / k : ℝ)
        (Set.pi Set.univ fun j => shortestArc ((fun x : Torus n => x j) '' X)) ∧
      Metric.diam (boxHull k hk X).realization ≤ Metric.diam X + 2 * (4 / k : ℝ)) ∧
    -- (3)
    (IsBoxHullAdmissible (Metric.cthickening (4 / k : ℝ) X) →
      ∀ c : GridCube k n, (c.realization ∩ X).Nonempty →
        c ∈ (boxHull k hk (Metric.cthickening (4 / k : ℝ) X)).cubes) := by
  sorry

end HSP.ChainModels
