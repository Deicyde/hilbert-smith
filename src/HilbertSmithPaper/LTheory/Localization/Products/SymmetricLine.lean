import Mathlib
import HilbertSmithPaper.LTheory.Bounded.Categories.BoundedDuality
import HilbertSmithPaper.LTheory.Localization.Products.BasedVectorSpaces

/-!
# The symmetric line

The complex `Λ` in `C_ℤ(ℚ)` has `Λ_0 = ℚ v_n` and `Λ_1 = ℚ e_{n+1/2}` in position `n`, every
other `Λ_r` a zero object, and `d e_{n+1/2} = v_{n+1} - v_n` (propagation `1`).

Lean: `Λ_r` is `ℚ^{d_r}` in every position, with `d_r = 1` for `r ∈ {0, 1}` and `d_r = 0`
otherwise, and the differential is given by constant `d_r × d_{r'}` matrices; when the source or
the target is `ℚ^0` the matrix is empty. `symLine.X_X` and `symLine.d_one_zero_apply` record
these defining formulas.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

namespace SymLine

/-- The dimension of `Λ_r` in each position: `1` for `r ∈ {0, 1}`, `0` otherwise. -/
private def dim (r : ℤ) : ℕ := if r = 0 ∨ r = 1 then 1 else 0

/-- The coefficients of `d : Λ_1 ⟶ Λ_0`: `d e_{n+1/2} = v_{n+1} - v_n`. -/
private def dCoef (m n : ℤ) : ℚ := if m = n + 1 then 1 else if m = n then -1 else 0

private lemma dCoef_eq_zero (m n : ℤ) (h : 1 < |m - n|) : dCoef m n = 0 := by
  rw [lt_abs] at h
  simp (disch := omega) only [dCoef, ite_eq_right]

/-- The differential of `Λ` from degree `r` to degree `r'`. -/
private noncomputable def d (r r' : ℤ) :
    (⟨fun _ => ⟨dim r⟩⟩ : Bounded FreeQ) ⟶ ⟨fun _ => ⟨dim r'⟩⟩ :=
  if r = 1 ∧ r' = 0 then
    ⟨fun m n => FreeQ.ofMatrix fun _ _ => dCoef m n, ⟨1, fun m n h => by
      change (fun _ _ => dCoef m n : Matrix _ _ ℚ) = 0
      ext
      simp [dCoef_eq_zero m n (by exact_mod_cast h)]⟩⟩
  else 0

end SymLine

/-- **The symmetric line** `Λ` in `C_ℤ(ℚ)`: `Λ_0 = ℚ v_n` and `Λ_1 = ℚ e_{n+1/2}` in position
`n`, every other `Λ_r` a zero object, with `d e_{n+1/2} = v_{n+1} - v_n` (propagation `1`). -/
noncomputable def symLine : ChainComplex (Bounded FreeQ) ℤ where
  X r := ⟨fun _ => ⟨SymLine.dim r⟩⟩
  d := SymLine.d
  shape r r' h := by
    simp only [ComplexShape.down_Rel] at h
    simp (disch := omega) only [SymLine.d, ite_eq_right]
  d_comp_d' r r' r'' _ _ := by
    unfold SymLine.d
    split_ifs <;> first | omega | simp

namespace symLine

/-- `Λ_r` is `ℚ` in every position for `r ∈ {0, 1}` and `ℚ^0` otherwise. -/
lemma X_X (r n : ℤ) : (symLine.X r).X n = ⟨if r = 0 ∨ r = 1 then 1 else 0⟩ := rfl

/-- The differential `d : Λ_1 ⟶ Λ_0`, `d e_{n+1/2} = v_{n+1} - v_n`. -/
lemma d_one_zero_apply (m n : ℤ) :
    (symLine.d 1 0).1 m n =
      FreeQ.ofMatrix fun _ _ => if m = n + 1 then 1 else if m = n then -1 else 0 := by
  change (SymLine.d 1 0).1 m n = _
  rw [SymLine.d, ite_eq_left ⟨rfl, rfl⟩]
  rfl

/-- `Λ_r` is a zero object for `r` outside `{0, 1}`. -/
lemma isZero_X {r : ℤ} (hr : ¬(r = 0 ∨ r = 1)) : IsZero (symLine.X r) := by
  have hd : SymLine.dim r = 0 := by simp [SymLine.dim, hr]
  refine ⟨fun Y => ⟨⟨0⟩, fun f => Bounded.hom_ext fun m n => ?_⟩,
    fun Y => ⟨⟨0⟩, fun f => Bounded.hom_ext fun m n => ?_⟩⟩
  · refine Matrix.ext fun i j => ?_
    have : IsEmpty (Fin (SymLine.dim r)) := by rw [hd]; infer_instance
    exact isEmptyElim (show Fin (SymLine.dim r) from j)
  · refine Matrix.ext fun i j => ?_
    have : IsEmpty (Fin (SymLine.dim r)) := by rw [hd]; infer_instance
    exact isEmptyElim (show Fin (SymLine.dim r) from i)

end symLine

end HSP
