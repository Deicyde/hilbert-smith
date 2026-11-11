import Mathlib
import HilbertSmithPaper.LTheory.Base.Complexes.StructureInvolution
import HilbertSmithPaper.LTheory.Bounded.Categories.BoundedDuality
import HilbertSmithPaper.LTheory.Localization.Products.BasedVectorSpaces

/-!
# The symmetric line

The complex `Λ` in `C_ℤ(ℚ)` has `Λ_0 = ℚ v_n` and `Λ_1 = ℚ e_{n+1/2}` in position `n`, every
other `Λ_r` zero, and `d e_{n+1/2} = v_{n+1} - v_n`. Its structure `λ ∈ M(Λ)_1` has components
`λ_0(e^*_{n+1/2}) = ½ (v_n + v_{n+1})` and `λ_1(v_n^*) = ½ (e_{n-1/2} + e_{n+1/2})`; it satisfies
`T λ = λ` and `∂ λ = 0`.

Lean: `Λ_r` is `ℚ^{d_r}` in every position, with `d_r = 1` for `r ∈ {0, 1}` and `d_r = 0`
otherwise. Every morphism used here is given by a family of constant matrices `c m n`, which
avoids case distinctions on the objects; when the source or the target is `ℚ^0` the matrix is
empty, so the formula in the other degrees is irrelevant.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

namespace SymLine

/-- The dimension of `Λ_r` in each position: `1` for `r ∈ {0, 1}`, `0` otherwise. -/
def dim (r : ℤ) : ℕ := if r = 0 ∨ r = 1 then 1 else 0

/-- The object `Λ_r` of `C_ℤ(ℚ)`. -/
abbrev obj (r : ℤ) : Bounded FreeQ := ⟨fun _ => ⟨dim r⟩⟩

/-- The family of constant matrices with entry `c m n` from position `n` to position `m`. -/
def fam {M N : Bounded FreeQ} (c : ℤ → ℤ → ℚ) : ∀ m n : ℤ, M.X n ⟶ N.X m :=
  fun m n => FreeQ.ofMatrix fun _ _ => c m n

private lemma fam_eq_zero {M N : Bounded FreeQ} (c : ℤ → ℤ → ℚ) {m n : ℤ} (h : c m n = 0) :
    fam (M := M) (N := N) c m n = 0 := by
  change (fun _ _ => c m n : Matrix _ _ ℚ) = 0
  ext i j
  simp [h]

/-- A morphism of propagation `1` given by constant matrices. -/
def homOf {M N : Bounded FreeQ} (c : ℤ → ℤ → ℚ) (hc : ∀ m n, 1 < |m - n| → c m n = 0) :
    M ⟶ N :=
  ⟨fam c, ⟨1, fun m n h => fam_eq_zero c (hc m n (by exact_mod_cast h))⟩⟩

private lemma sum_entry {X Y : FreeQ} (s : Finset ℤ) (F : ℤ → (X ⟶ Y)) (i : Fin Y.dim)
    (j : Fin X.dim) : FreeQ.toMatrix (∑ m ∈ s, F m) i j = ∑ m ∈ s, FreeQ.toMatrix (F m) i j :=
  map_sum (⟨⟨fun f : X ⟶ Y => FreeQ.toMatrix f i j, rfl⟩, fun _ _ => rfl⟩ : (X ⟶ Y) →+ ℚ) F s

private lemma homOf_comp_entry {M N P : Bounded FreeQ} (c c' : ℤ → ℤ → ℚ)
    (hc : ∀ m n, 1 < |m - n| → c m n = 0) (hc' : ∀ m n, 1 < |m - n| → c' m n = 0)
    (l n : ℤ) (i : Fin (P.X l).dim) (j : Fin (M.X n).dim) :
    FreeQ.toMatrix ((homOf (M := M) (N := N) c hc ≫ homOf (N := P) c' hc').1 l n) i j =
      ∑ m ∈ Finset.Icc (n - 1) (n + 1), ((N.X m).dim : ℚ) * (c' l m * c m n) := by
  rw [Bounded.comp_apply, Bounded.compF_eq_sum _ _ l n (Finset.Icc (n - 1) (n + 1))
    (fun m hm => by
      rw [Finset.mem_Icc] at hm
      change fam c m n ≫ fam c' l m = 0
      rw [fam_eq_zero c (hc m n (by rw [lt_abs]; omega)), zero_comp]), sum_entry]
  refine Finset.sum_congr rfl fun m _ => ?_
  change ∑ k : Fin (N.X m).dim, c' l m * c m n = _
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

private lemma dualHom_homOf {M N : Bounded FreeQ} (c : ℤ → ℤ → ℚ)
    (hc : ∀ m n, 1 < |m - n| → c m n = 0) :
    dualHom (homOf (M := M) (N := N) c hc) =
      homOf (fun m n => c n m) (fun m n h => hc n m (by rwa [abs_sub_comm])) :=
  Bounded.hom_ext fun _ _ => rfl

/-- Morphisms between objects of `C_ℤ(ℚ)` agree when every block has an empty side. -/
private lemma hom_ext_empty {M N : Bounded FreeQ} (f g : M ⟶ N)
    (h : ∀ m n, IsEmpty (Fin (N.X m).dim) ∨ IsEmpty (Fin (M.X n).dim)) : f = g := by
  refine Bounded.hom_ext fun m n => ?_
  refine Matrix.ext fun i j => ?_
  rcases h m n with h | h
  · exact isEmptyElim i
  · exact isEmptyElim j

private lemma isEmpty_dim {r : ℤ} (hr : ¬(r = 0 ∨ r = 1)) : IsEmpty (Fin (dim r)) := by
  rw [show dim r = 0 by simp [dim, hr]]
  infer_instance

private lemma dim_zero : dim 0 = 1 := by simp [dim]

private lemma dim_one : dim 1 = 1 := by simp [dim]

/-- The coefficients of `d : Λ_1 ⟶ Λ_0`: `d e_{n+1/2} = v_{n+1} - v_n`. -/
def dCoef (m n : ℤ) : ℚ := if m = n + 1 then 1 else if m = n then -1 else 0

/-- The coefficients of `λ_0 : Λ_1^* ⟶ Λ_0`: `e^*_{n+1/2} ↦ ½ (v_n + v_{n+1})`. -/
def lam0 (m n : ℤ) : ℚ := if m = n ∨ m = n + 1 then 1 / 2 else 0

/-- The coefficients of `λ_1 : Λ_0^* ⟶ Λ_1`: `v_n^* ↦ ½ (e_{n-1/2} + e_{n+1/2})`. -/
def lam1 (m n : ℤ) : ℚ := if m + 1 = n ∨ m = n then 1 / 2 else 0

private lemma dCoef_eq_zero (m n : ℤ) (h : 1 < |m - n|) : dCoef m n = 0 := by
  rw [lt_abs] at h
  simp (disch := omega) only [dCoef, ite_eq_right]

private lemma lam0_eq_zero (m n : ℤ) (h : 1 < |m - n|) : lam0 m n = 0 := by
  rw [lt_abs] at h
  simp (disch := omega) only [lam0, ite_eq_right]

private lemma lam1_eq_zero (m n : ℤ) (h : 1 < |m - n|) : lam1 m n = 0 := by
  rw [lt_abs] at h
  simp (disch := omega) only [lam1, ite_eq_right]

/-- The differential of `Λ` from degree `r` to degree `r'`. -/
noncomputable def d (r r' : ℤ) : obj r ⟶ obj r' :=
  if r = 1 ∧ r' = 0 then homOf dCoef dCoef_eq_zero else 0

end SymLine

open SymLine in
/-- **The symmetric line** `Λ` in `C_ℤ(ℚ)`: `Λ_0 = ℚ v_n` and `Λ_1 = ℚ e_{n+1/2}` in position
`n`, every other `Λ_r` zero, with `d e_{n+1/2} = v_{n+1} - v_n` (propagation `1`). -/
noncomputable def symLine : ChainComplex (Bounded FreeQ) ℤ where
  X := obj
  d := d
  shape r r' h := by
    simp only [ComplexShape.down_Rel] at h
    simp (disch := omega) only [d, ite_eq_right]
  d_comp_d' r r' r'' _ _ := by
    unfold d
    split_ifs <;> first | omega | simp

namespace symLine

open SymLine

/-- The structure `λ ∈ M(Λ)_1`, with components `λ_0` and `λ_1` (and zero elsewhere). -/
noncomputable def str : (StructureCx symLine).X 1 := fun x =>
  if x.1.1 = 0 then homOf lam0 lam0_eq_zero else homOf lam1 lam1_eq_zero

private lemma str_zero (h : (0 : ℤ) + 1 = 1) :
    str ⟨(0, 1), h⟩ = homOf lam0 lam0_eq_zero :=
  ite_eq_left rfl

private lemma str_one (h : (1 : ℤ) + 0 = 1) :
    str ⟨(1, 0), h⟩ = homOf lam1 lam1_eq_zero :=
  ite_eq_right one_ne_zero

private lemma d_one_zero : symLine.d 1 0 = homOf dCoef dCoef_eq_zero := by
  change SymLine.d 1 0 = _
  rw [SymLine.d]
  exact ite_eq_left ⟨rfl, rfl⟩

/-- `T λ = λ`. -/
theorem str_T : (StructureCx.T symLine).f 1 str = str := by
  funext x
  obtain ⟨⟨p, q⟩, h⟩ := x
  rw [StructureCx.T_apply]
  by_cases hp : p = 0 ∨ p = 1
  · rcases hp with rfl | rfl
    · obtain rfl : q = 1 := by omega
      rw [str_one, str_zero, dualHom_homOf]
      simp only [mul_one, Int.negOnePow_zero, one_smul, eqToHom_refl, Category.comp_id]
      congr 1
      funext m n
      simp only [lam0, lam1]
      congr 1
      exact propext (by omega)
    · obtain rfl : q = 0 := by omega
      rw [str_zero, str_one, dualHom_homOf]
      simp only [mul_zero, Int.negOnePow_zero, one_smul, eqToHom_refl, Category.comp_id]
      congr 1
      funext m n
      simp only [lam0, lam1]
      congr 1
      exact propext (by omega)
  · exact hom_ext_empty _ _ fun _ _ => Or.inl (isEmpty_dim hp)

private lemma cycle_coef (l n : ℤ) :
    ∑ m ∈ Finset.Icc (n - 1) (n + 1), (dCoef l m * lam1 m n + lam0 l m * dCoef n m) = 0 := by
  have hI : Finset.Icc (n - 1) (n + 1) = {n - 1, n, n + 1} := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [hI, Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
    Finset.sum_insert (by simp only [Finset.mem_singleton]; omega), Finset.sum_singleton]
  rcases (by omega : l ≤ n - 3 ∨ l = n - 2 ∨ l = n - 1 ∨ l = n ∨ l = n + 1 ∨ l = n + 2 ∨
    n + 3 ≤ l) with h | h | h | h | h | h | h <;>
  · simp (disch := omega) only [dCoef, lam0, lam1, ite_eq_left, ite_eq_right]
    norm_num

/-- `∂ λ = 0`. -/
theorem str_cycle : (StructureCx symLine).d 1 0 str = 0 := by
  funext x
  obtain ⟨⟨p, q⟩, h⟩ := x
  by_cases hpq : p = 0 ∧ q = 0
  · obtain ⟨rfl, rfl⟩ := hpq
    rw [StructureCx.d_apply symLine 1 0 str 0 0 h 1 1 rfl rfl, str_one, str_zero, d_one_zero,
      Int.negOnePow_zero, one_smul, dualHom_homOf]
    refine Bounded.hom_ext fun l n => Matrix.ext fun i j => ?_
    rw [Bounded.add_apply]
    refine (congrArg₂ (· + ·)
      (homOf_comp_entry (M := dual (symLine.X 0)) (N := symLine.X 1) (P := symLine.X 0)
        lam1 dCoef lam1_eq_zero dCoef_eq_zero l n i j)
      (homOf_comp_entry (M := dual (symLine.X 0)) (N := dual (symLine.X 1)) (P := symLine.X 0)
        (fun m n => dCoef n m) lam0 _ lam0_eq_zero l n i j)).trans ?_
    change ∑ m ∈ Finset.Icc (n - 1) (n + 1), ((dim 1 : ℕ) : ℚ) * (dCoef l m * lam1 m n) +
      ∑ m ∈ Finset.Icc (n - 1) (n + 1), ((dim 1 : ℕ) : ℚ) * (lam0 l m * dCoef n m) = 0
    rw [dim_one, Nat.cast_one]
    simp only [one_mul, ← Finset.sum_add_distrib]
    exact cycle_coef l n
  · refine hom_ext_empty _ _ fun _ _ => ?_
    by_cases hp : p = 0 ∨ p = 1
    · exact Or.inr (isEmpty_dim (r := q) (by omega))
    · exact Or.inl (isEmpty_dim hp)

end symLine

end HSP
