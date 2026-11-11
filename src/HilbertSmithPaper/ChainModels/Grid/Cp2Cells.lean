import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.BasedVectorSpaces
import HilbertSmithPaper.LTheory.Base.Pairs.SymmetricPoincareComplex
import HilbertSmithPaper.LTheory.Base.Complexes.CycleChainMap

/-!
# Cells of `CP²`

The cellular chains `P` of `CP²`: `P_r = ℚ e_r` for `r ∈ {0, 2, 4}`, zero otherwise, with zero
differential, and the structure `φ_P : P^{4-*} → P`, `e_r^* ↦ e_{4-r}`, a strict symmetric
Poincaré structure of dimension `4` over based vector spaces with inverse `b_P`.

## Encoding

* `P` is a `ChainComplex FreeQ ℤ` with `P_r = ⟨cp2Dim r⟩`; the dual of `ℚ^d` is `ℚ^d`.
* Every component `φ_{p,q} : (P_q)^* → P_p` (`p + q = 4`) is the all-ones matrix: the `1 × 1`
  matrix `1` when `p, q ∈ {0,2,4}`, and the empty matrix otherwise; likewise `b_P`.
* `cp2Cells : SymPoincare FreeQ 4` (the declaration of the article) packages `P` and `φ_P` with
  `∂φ_P = 0`, `T φ_P = φ_P` (`r(4-r)` is even) and the Poincaré property, witnessed by the strict
  inverse `b_P` (zero homotopies). The middle form, the fundamental cycle and the augmentation are
  companions.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.ChainModels

open FreeQ DualCat

/-- The number of cells of `CP²` in degree `r`: `1` for `r ∈ {0, 2, 4}`, else `0`. -/
def cp2Dim : ℤ → ℕ
  | .ofNat 0 => 1
  | .ofNat 2 => 1
  | .ofNat 4 => 1
  | _ => 0

private lemma cp2Dim_eq (r : ℤ) : cp2Dim r = if r = 0 ∨ r = 2 ∨ r = 4 then 1 else 0 :=
  match r with
  | .ofNat 0 => rfl
  | .ofNat 1 => rfl
  | .ofNat 2 => rfl
  | .ofNat 3 => rfl
  | .ofNat 4 => rfl
  | .ofNat (n + 5) => by
    show 0 = _
    rw [eq_comm, ite_eq_right_iff]
    intro h
    simp only [Int.ofNat_eq_natCast] at h
    omega
  | .negSucc n => by
    show 0 = _
    rw [eq_comm, ite_eq_right_iff]
    intro h
    rw [Int.negSucc_eq] at h
    omega

/-- The cellular chain complex `P` of `CP²`, with zero differential. -/
def cp2Complex : ChainComplex FreeQ ℤ :=
  ChainComplex.of (fun r => ⟨cp2Dim r⟩) (fun _ => 0) fun _ => zero_comp

private lemma cp2Complex_d (i j : ℤ) : cp2Complex.d i j = 0 := by
  show ChainComplex.of.d (fun r => (⟨cp2Dim r⟩ : FreeQ)) (fun _ => 0) i j = 0
  unfold ChainComplex.of.d
  split_ifs <;> simp

/-- The structure `φ_P`: `φ_{p,q} : (P_q)^* → P_p` sends `e_q^*` to `e_p` (`p + q = 4`). -/
def cp2Structure : (StructureCx cp2Complex).X 4 :=
  fun _ => ofMatrix (Matrix.of fun _ _ => 1)

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

/-- The inverse `b_P : P → P^{4-*}` of `φ_P`, `e_{4-r} ↦ e_r^*`. -/
def cp2Inverse : cp2Complex ⟶ dualCx cp2Complex 4 where
  f _ := ofMatrix (Matrix.of fun _ _ => 1)
  comm' i j _ := by
    simp only [cp2Complex_d, zero_comp, dualHom_zero, smul_zero, comp_zero]

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

/-- The induced form on `P_2` is `⟨1⟩`: `φ_{2,2} = 1`. -/
lemma cp2Cells_middle_form : cp2Cells.φ ⟨(2, 2), rfl⟩ = 𝟙 _ := by
  have h : (Matrix.of fun _ _ => (1 : ℚ) : Matrix (Fin 1) (Fin 1) ℚ) = 1 := by
    ext a b; fin_cases a; fin_cases b; rfl
  exact h

/-- The fundamental cycle `e_4`, as a column. -/
def cp2Fundamental : (⟨1⟩ : FreeQ) ⟶ cp2Complex.X 4 :=
  ofMatrix (Matrix.of fun _ _ => 1)

/-- The augmentation `ε e_0 = 1`. -/
def cp2Aug : cp2Complex.X 0 ⟶ (⟨1⟩ : FreeQ) :=
  ofMatrix (Matrix.of fun _ _ => 1)

end HSP.ChainModels
