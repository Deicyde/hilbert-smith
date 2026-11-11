import Mathlib

/-!
# The torus

`𝕋ⁿ = (ℝ/4ℤ)ⁿ`, with the lift `x ↦ x̃ ∈ [-2,2)ⁿ`, the quotient map `q : ℝⁿ → 𝕋ⁿ`, the two
metrics `d_∞` and `d_2`, and the closed `d_∞`-neighbourhoods `N_r(X)`.

## Encoding

* `𝕋ⁿ` is `Fin n → AddCircle (4 : ℝ)`. Mathlib's metric on it is the maximum of the circle
  distances, so `d_∞` is `dist`, and its norm `‖x‖` is `d_∞(x, 0)`.
* `ℝⁿ` is `EuclideanSpace ℝ (Fin n)`, as in the local-data chapter. The lift takes values there;
  `|x̃|_∞` is the sup norm `‖WithLp.ofLp x̃‖`.
* `d_2(x,y) = (∑ⱼ d(xⱼ,yⱼ)²)^{1/2}` is `Torus.dist₂`; it is the quotient Euclidean metric.
* `N_r(X)` is `Metric.cthickening r X`, the points at `d_∞`-distance at most `r` from `X`.
* The instance `Fact (0 < 4)`, which Mathlib's `AddCircle` API needs, lives here.
-/

namespace HSP.ChainModels

/-- `4 > 0`, for the circle `ℝ/4ℤ`. -/
instance fact_zero_lt_four : Fact ((0 : ℝ) < 4) := ⟨by norm_num⟩

/-- The torus `𝕋ⁿ = (ℝ/4ℤ)ⁿ`; its `dist` is `d_∞`, the maximum of the circle distances. -/
abbrev Torus (n : ℕ) : Type := Fin n → AddCircle (4 : ℝ)

namespace Torus

variable {n : ℕ}

/-- The lift `x̃ ∈ [-2,2)ⁿ` of `x ∈ 𝕋ⁿ`, as a vector of `ℝⁿ`. -/
noncomputable def lift (x : Torus n) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun j => (AddCircle.equivIco 4 (-2) (x j) : ℝ)

/-- The quotient map `q : ℝⁿ → 𝕋ⁿ`. -/
def proj (y : EuclideanSpace ℝ (Fin n)) : Torus n :=
  fun j => (y j : AddCircle (4 : ℝ))

/-- The quotient Euclidean metric `d_2(x,y) = (∑ⱼ d(xⱼ,yⱼ)²)^{1/2}`. -/
noncomputable def dist₂ (x y : Torus n) : ℝ :=
  √(∑ j, dist (x j) (y j) ^ 2)

/-- The closed `d_∞`-neighbourhood `N_r(X)` of radius `r`. -/
noncomputable abbrev nbhd (r : ℝ) (X : Set (Torus n)) : Set (Torus n) :=
  Metric.cthickening r X

/-- The lift lies in `[-2,2)ⁿ`. -/
lemma lift_mem (x : Torus n) (j : Fin n) : lift x j ∈ Set.Ico (-2 : ℝ) 2 := by
  have h := (AddCircle.equivIco 4 (-2) (x j)).2
  norm_num at h
  exact h

/-- `q(x̃) = x`. -/
@[simp]
lemma proj_lift (x : Torus n) : proj (lift x) = x := by
  funext j; simp [proj, lift]

/-- `d_∞ ≤ d_2`. -/
lemma dist_le_dist₂ (x y : Torus n) : dist x y ≤ dist₂ x y := by
  refine (dist_pi_le_iff (Real.sqrt_nonneg _)).2 fun j => ?_
  refine Real.le_sqrt_of_sq_le ?_
  exact Finset.single_le_sum (f := fun j => dist (x j) (y j) ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ j)

/-- `d_2 ≤ √n d_∞`. -/
lemma dist₂_le (x y : Torus n) : dist₂ x y ≤ √n * dist x y := by
  rw [dist₂, ← Real.sqrt_sq dist_nonneg, ← Real.sqrt_mul (Nat.cast_nonneg n)]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ j, dist (x j) (y j) ^ 2 ≤ ∑ _j : Fin n, dist x y ^ 2 :=
        Finset.sum_le_sum fun j _ => pow_le_pow_left₀ dist_nonneg (dist_le_pi_dist x y j) 2
    _ = n * dist x y ^ 2 := by simp

end Torus

end HSP.ChainModels
