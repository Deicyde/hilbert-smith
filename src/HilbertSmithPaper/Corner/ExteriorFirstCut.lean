import Mathlib
import HilbertSmithPaper.Corner.Exterior
import HilbertSmithPaper.Corner.CutSets

/-!
# The exterior lies in the first cut

For `n ≥ 1`, `R > 0` and `0 < s < R / √n`: `Z₀ ⊆ A_1` and `Z₀ ∩ B_1 = ∅`. Every `x ∈ B_1 = [-s, s]^n`
has `|x| ≤ s √n < R`, and `∞ ∉ B_1`; hence `Z₀ ⊆ Y_0 \ B_1 ⊆ A_1`.

The proof does not use `R > 0` (it follows from the other two inequalities); it is kept, named
with a leading underscore, as part of the article's setting.
-/

namespace HSP.Corner

/-- The exterior lies in the first cut: `Z₀ ⊆ A_1` and `Z₀ ∩ B_1 = ∅`. -/
theorem exterior_first_cut (n : ℕ) (hn : 1 ≤ n) (R s : ℝ) (_hR : 0 < R) (hs : 0 < s)
    (hsR : s < R / √n) :
    exterior n R ⊆ cutA n s 1 ∧ exterior n R ∩ cutB n s 1 = ∅ := by
  have hdisj : exterior n R ∩ cutB n s 1 = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hx hB
    obtain ⟨y, hy, rfl⟩ := hB
    have hR : R ≤ ‖y‖ := by simpa [exterior] using hx
    have hsum : ∑ k, ‖y k‖ ^ 2 ≤ n * s ^ 2 := by
      calc ∑ k, ‖y k‖ ^ 2 ≤ ∑ _k : Fin n, s ^ 2 := Finset.sum_le_sum fun k _ => by
            have hk := (hy k).1 (by have := k.isLt; omega)
            rw [Real.norm_eq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) hk 2
        _ = n * s ^ 2 := by simp
    have hle : ‖y‖ ≤ √n * s := by
      rw [EuclideanSpace.norm_eq]
      calc √(∑ k, ‖y k‖ ^ 2) ≤ √(n * s ^ 2) := Real.sqrt_le_sqrt hsum
        _ = √n * s := by rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hs.le]
    have hn' : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
    have hlt : √n * s < R := by
      rw [lt_div_iff₀ hn'] at hsR; linarith
    linarith
  refine ⟨fun x hx => ?_, hdisj⟩
  show x ∈ closure (cutY n s (1 - 1) \ cutB n s 1)
  refine subset_closure ⟨Set.mem_univ x, fun hB => ?_⟩
  have hmem : x ∈ exterior n R ∩ cutB n s 1 := ⟨hx, hB⟩
  rw [hdisj] at hmem
  exact hmem

end HSP.Corner
