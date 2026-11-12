import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Cp2.Cp2Structure
import HilbertSmithPaper.ChainModels.Grid.Cp2.Cp2Inverse
import HilbertSmithPaper.LTheory.Base.Pairs.SymmetricPoincareComplex
import HilbertSmithPaper.LTheory.Base.Complexes.CycleChainMap

/-!
# Cells of `CP²`

The cellular chains `P` of `CP²` with the structure `φ_P` form a strict `4`-dimensional symmetric
Poincaré complex over based vector spaces, with inverse `b_P`.

## Encoding

`cp2Cells : SymPoincare FreeQ 4` (the declaration of the article) packages `P` and `φ_P` with
`∂φ_P = 0`, `T φ_P = φ_P` (`r(4-r)` is even) and the Poincaré property, witnessed by the strict
inverse `b_P` (zero homotopies).
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.ChainModels

open FreeQ DualCat

private lemma cp2Structure_cycle : (StructureCx cp2Complex).d 4 (4 - 1) cp2Structure = 0 := by
  funext ⟨⟨p, q⟩, h⟩
  rw [StructureCx.d_apply cp2Complex 4 (4 - 1) cp2Structure p q h (4 - q) (4 - p) (by omega)
    (by omega)]
  simp only [cp2Complex_d, comp_zero, dualHom_zero, zero_comp, smul_zero, add_zero]
  rfl

private lemma even_of_cp2Dim_ne {r : ℤ} (h : cp2Dim r ≠ 0) : Even r := by
  rw [cp2Dim_eq] at h
  split_ifs at h with h'
  · rcases h' with rfl | rfl | rfl <;> decide
  · exact absurd rfl h

private lemma cp2Structure_symmetric :
    (StructureCx.T cp2Complex).f 4 cp2Structure = cp2Structure := by
  funext ⟨⟨p, q⟩, h⟩
  rw [StructureCx.T_apply]
  refine Matrix.ext fun a b => ?_
  have hp : Even p := even_of_cp2Dim_ne fun e => (Fin.cast e a).elim0
  have hq : Even q := even_of_cp2Dim_ne fun e => (Fin.cast e b).elim0
  rw [Int.negOnePow_even _ (hp.mul_right q), one_smul, eqToHom_refl, Category.comp_id]
  rfl

private lemma cp2Dim_symm (r : ℤ) : cp2Dim (4 - r) = cp2Dim r := by
  rw [cp2Dim_eq, cp2Dim_eq]
  congr 1
  apply propext
  omega

private lemma ones_mul_ones_of_eq {a b : ℕ} (h : a = b) (hb : b ≤ 1) :
    (Matrix.of fun _ _ => (1 : ℚ) : Matrix (Fin a) (Fin b) ℚ) *
      (Matrix.of fun _ _ => (1 : ℚ) : Matrix (Fin b) (Fin a) ℚ) = 1 := by
  subst h
  refine Matrix.ext fun i j => ?_
  have ha : a = 1 := by have := i.2; omega
  subst ha
  have : i = j := Subsingleton.elim i j
  subst this
  simp [Matrix.mul_apply]

private lemma cp2Dim_le (r : ℤ) : cp2Dim r ≤ 1 := by
  rw [cp2Dim_eq]; split_ifs <;> norm_num

/-- *Cells of `CP²`*: the strict `4`-dimensional symmetric Poincaré complex `(P, φ_P)` over based
vector spaces. -/
def cp2Cells : SymPoincare FreeQ 4 where
  C := cp2Complex
  φ := cp2Structure
  bounded r hr := by
    have h0 : cp2Dim r = 0 := by rw [cp2Dim_eq, ite_eq_right_iff]; omega
    show IsZero (⟨cp2Dim r⟩ : FreeQ)
    rw [h0]
    exact isZero_zero
  cycle := cp2Structure_cycle
  symmetric := cp2Structure_symmetric
  poincare := ⟨{
    hom := StructureCx.toHom cp2Structure cp2Structure_cycle
    inv := cp2Inverse
    homotopyHomInvId := Homotopy.ofEq (by
      ext r
      exact ones_mul_ones_of_eq (a := cp2Dim (4 - r)) (b := cp2Dim r) (cp2Dim_symm r)
        (cp2Dim_le r))
    homotopyInvHomId := Homotopy.ofEq (by
      ext r
      exact ones_mul_ones_of_eq (a := cp2Dim r) (b := cp2Dim (4 - r)) (cp2Dim_symm r).symm
        (cp2Dim_le (4 - r))) }, rfl⟩

end HSP.ChainModels
