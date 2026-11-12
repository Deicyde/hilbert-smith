import Mathlib
import HilbertSmithPaper.ChainModels.Approximations.Maps.TrackMapEuclid

/-!
# Completed and track maps are the identity off `B(0,3/2)`

For `|x| ≥ 3/2`, `â(x) = x` and `L_{a,b,c,t}(x) = x`.

## Encoding

`identity_off_ball A` (the declaration of the article) is the conjunction of the two statements.
-/

namespace HSP.ChainModels

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- `â` and `L_{a,b,c,t}` are the identity off `B(0,3/2)`. -/
lemma identity_off_ball (A : LocalDatum p n D ρplus) :
    (∀ (a : ℤ_[p]) (x : EuclideanSpace ℝ (Fin n)), 3 / 2 ≤ ‖x‖ → completedMapEuclid A a x = x) ∧
      ∀ (a b c : ℤ_[p]) (t : unitInterval) (x : EuclideanSpace ℝ (Fin n)), 3 / 2 ≤ ‖x‖ →
        trackMapEuclid A a b c t x = x := by
  have h1 : ∀ (a : ℤ_[p]) (x : EuclideanSpace ℝ (Fin n)), 3 / 2 ≤ ‖x‖ →
      completedMapEuclid A a x = x := by
    intro a x hx
    have hθ : completedCutoff x = 0 := by
      rw [completedCutoff, max_eq_left (by linarith), min_eq_right zero_le_one]
    unfold completedMapEuclid
    split_ifs <;> simp [hθ]
  refine ⟨h1, fun a b c t x hx => ?_⟩
  simp only [trackMapEuclid, h1 _ _ hx, ← add_smul, sub_add_cancel, one_smul]

end HSP.ChainModels
