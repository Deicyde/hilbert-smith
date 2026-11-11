import Mathlib
import HilbertSmithPaper.LTheory.Base.Complexes.StructureComplex
import HilbertSmithPaper.LTheory.Localization.Products.SymmetricLine

/-!
# Structure of the symmetric line

The structure `λ ∈ M(Λ)_1` has components `λ_0 : Λ_1^* ⟶ Λ_0`,
`e^*_{n+1/2} ↦ ½ (v_n + v_{n+1})`, and `λ_1 : Λ_0^* ⟶ Λ_1`, `v_n^* ↦ ½ (e_{n-1/2} + e_{n+1/2})`,
both of propagation `1`, all other components being zero.

Lean: every component is given by constant matrices (empty when a side is `ℚ^0`); the component
at `(p, q)` uses the `λ_0` coefficients for `p = 0` and the `λ_1` coefficients otherwise.
`symLine.str_apply` records this defining formula.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

/-- The coefficient of `λ_0` (`p = 0`) or `λ_1` (otherwise) from position `n` to position `m`. -/
private def lamCoef (p m n : ℤ) : ℚ :=
  if p = 0 then (if m = n ∨ m = n + 1 then 1 / 2 else 0) else (if m + 1 = n ∨ m = n then 1 / 2 else 0)

private lemma lamCoef_eq_zero (p m n : ℤ) (h : 1 < |m - n|) : lamCoef p m n = 0 := by
  rw [lt_abs] at h
  unfold lamCoef
  split_ifs <;> first | rfl | omega

/-- **Structure of the symmetric line.** `λ ∈ M(Λ)_1`, with components
`λ_0(e^*_{n+1/2}) = ½ (v_n + v_{n+1})` and `λ_1(v_n^*) = ½ (e_{n-1/2} + e_{n+1/2})`. -/
noncomputable def symLine.str : (StructureCx symLine).X 1 := fun x =>
  ⟨fun m n => FreeQ.ofMatrix fun _ _ => lamCoef x.1.1 m n, ⟨1, fun m n h => by
    change (fun _ _ => lamCoef x.1.1 m n : Matrix _ _ ℚ) = 0
    ext
    simp [lamCoef_eq_zero x.1.1 m n (by exact_mod_cast h)]⟩⟩

/-- The components of `λ`: the `λ_0` coefficients at `p = 0`, the `λ_1` coefficients otherwise. -/
lemma symLine.str_apply (p q : ℤ) (h : p + q = 1) (m n : ℤ) :
    (symLine.str ⟨(p, q), h⟩).1 m n = FreeQ.ofMatrix fun _ _ =>
      if p = 0 then (if m = n ∨ m = n + 1 then 1 / 2 else 0)
      else (if m + 1 = n ∨ m = n then 1 / 2 else 0) :=
  rfl

end HSP
