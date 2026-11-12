import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Cp2.Cp2Cells
import HilbertSmithPaper.ChainModels.Grid.Cp2.Cp2Complex

/-!
# The CP² inverse inverts the structure

`(b_P)_r (φ_P)_{r,4-r} = 1` on `P_r` and `(φ_P)_{r,4-r} (b_P)_r =
1` on `P_{4-r}^*`: both are products
of all-ones matrices of the same size `≤ 1`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.ChainModels

open FreeQ DualCat

private lemma ones_mul_ones {a b : ℕ} (h : a = b) (hb : b ≤ 1) :
    (Matrix.of fun _ _ => (1 : ℚ) : Matrix (Fin a) (Fin b) ℚ) *
      (Matrix.of fun _ _ => (1 : ℚ) : Matrix (Fin b) (Fin a) ℚ) = 1 := by
  subst h
  refine Matrix.ext fun i j => ?_
  have ha : a = 1 := by have := i.2; omega
  subst ha
  have : i = j := Subsingleton.elim i j
  subst this
  simp [Matrix.mul_apply]

/-- *The CP² inverse inverts the structure*: `b_P` and `φ_P` are inverse in every degree. -/
lemma cp2Inverse_comp_cp2Structure (r : ℤ) :
    cp2Inverse.f r ≫ cp2Structure ⟨(r, 4 - r), by ring⟩ = 𝟙 _ ∧
      cp2Structure ⟨(r, 4 - r), by ring⟩ ≫ cp2Inverse.f r = 𝟙 _ := by
  have hs : cp2Dim (4 - r) = cp2Dim r := by
    rw [cp2Dim_eq, cp2Dim_eq]
    congr 1
    apply propext
    omega
  have hle : ∀ s, cp2Dim s ≤ 1 := fun s => by rw [cp2Dim_eq]; split_ifs <;> norm_num
  exact ⟨ones_mul_ones (a := cp2Dim r) (b := cp2Dim (4 - r)) hs.symm (hle _),
    ones_mul_ones (a := cp2Dim (4 - r)) (b := cp2Dim r) hs (hle _)⟩

end HSP.ChainModels
