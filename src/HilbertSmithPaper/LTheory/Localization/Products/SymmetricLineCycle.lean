import Mathlib
import HilbertSmithPaper.LTheory.Base.Complexes.StructureInvolution
import HilbertSmithPaper.LTheory.Localization.Products.SymmetricLineStructure

/-!
# The symmetric line is a symmetric complex

`T λ = λ` and `∂ λ = 0`, so `(Λ, λ)` is a strict `1`-dimensional symmetric complex. Both are
direct checks on the constant matrices of `λ` and `d`: the components of `T λ` are `λ_1^*` and
`λ_0^*` (the sign `(-1)^{r(1-r)}` is `1`), and `(∂λ)_0 = d λ_1 + λ_0 d^*` vanishes.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

private lemma sum_entry {X Y : FreeQ} (s : Finset ℤ) (F : ℤ → (X ⟶ Y)) (i : Fin Y.dim)
    (j : Fin X.dim) : FreeQ.toMatrix (∑ m ∈ s, F m) i j = ∑ m ∈ s, FreeQ.toMatrix (F m) i j :=
  map_sum (⟨⟨fun f : X ⟶ Y => FreeQ.toMatrix f i j, rfl⟩, fun _ _ => rfl⟩ : (X ⟶ Y) →+ ℚ) F s

private lemma ofMatrix_const_eq_zero {X Y : FreeQ} {c : ℚ} (h : c = 0) :
    (FreeQ.ofMatrix fun _ _ => c : X ⟶ Y) = 0 := by
  change (fun _ _ => c : Matrix _ _ ℚ) = 0
  ext
  simp [h]

/-- The entries of a composite of constant-matrix families of propagation `≤ 1`. -/
private lemma comp_entry {M N P : Bounded FreeQ} (f : M ⟶ N) (g : N ⟶ P) (c c' : ℤ → ℤ → ℚ)
    (hf : ∀ m n, f.1 m n = FreeQ.ofMatrix fun _ _ => c m n)
    (hg : ∀ m n, g.1 m n = FreeQ.ofMatrix fun _ _ => c' m n)
    (hc : ∀ m n, 1 < |m - n| → c m n = 0) (l n : ℤ) (i : Fin (P.X l).dim)
    (j : Fin (M.X n).dim) :
    FreeQ.toMatrix ((f ≫ g).1 l n) i j =
      ∑ m ∈ Finset.Icc (n - 1) (n + 1), ((N.X m).dim : ℚ) * (c' l m * c m n) := by
  rw [Bounded.comp_apply, Bounded.compF_eq_sum _ _ l n (Finset.Icc (n - 1) (n + 1))
    (fun m hm => by
      rw [Finset.mem_Icc] at hm
      rw [hf, ofMatrix_const_eq_zero (hc m n (by rw [lt_abs]; omega)), zero_comp]), sum_entry]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hf, hg]
  change ∑ k : Fin (N.X m).dim, c' l m * c m n = _
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Morphisms between objects of `C_ℤ(ℚ)` agree when every block has an empty side. -/
private lemma hom_ext_empty {M N : Bounded FreeQ} (f g : M ⟶ N)
    (h : ∀ m n, IsEmpty (Fin (N.X m).dim) ∨ IsEmpty (Fin (M.X n).dim)) : f = g := by
  refine Bounded.hom_ext fun m n => ?_
  refine Matrix.ext fun i j => ?_
  rcases h m n with h | h
  · exact isEmptyElim i
  · exact isEmptyElim j

private lemma isEmpty_X {r : ℤ} (hr : ¬(r = 0 ∨ r = 1)) (n : ℤ) :
    IsEmpty (Fin ((symLine.X r).X n).dim) := by
  rw [symLine.X_X]
  simp only [hr, ite_false]
  infer_instance

private lemma dim_one (m : ℤ) : (((symLine.X 1).X m).dim : ℚ) = 1 := by
  rw [symLine.X_X]
  simp

private lemma dim_one' (m : ℤ) : (((dual (symLine.X 1)).X m).dim : ℚ) = 1 := dim_one m

private def cD (m n : ℤ) : ℚ := if m = n + 1 then 1 else if m = n then -1 else 0

private def c0 (m n : ℤ) : ℚ := if m = n ∨ m = n + 1 then 1 / 2 else 0

private def c1 (m n : ℤ) : ℚ := if m + 1 = n ∨ m = n then 1 / 2 else 0

private lemma cD_eq_zero (m n : ℤ) (h : 1 < |m - n|) : cD m n = 0 := by
  rw [lt_abs] at h
  simp (disch := omega) only [cD, ite_eq_right]

private lemma cD'_eq_zero (m n : ℤ) (h : 1 < |m - n|) : cD n m = 0 :=
  cD_eq_zero n m (by rwa [abs_sub_comm])

private lemma c1_eq_zero (m n : ℤ) (h : 1 < |m - n|) : c1 m n = 0 := by
  rw [lt_abs] at h
  simp (disch := omega) only [c1, ite_eq_right]

private lemma cycle_coef (l n : ℤ) :
    ∑ m ∈ Finset.Icc (n - 1) (n + 1), (cD l m * c1 m n + c0 l m * cD n m) = 0 := by
  have hI : Finset.Icc (n - 1) (n + 1) = {n - 1, n, n + 1} := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [hI, Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
    Finset.sum_insert (by simp only [Finset.mem_singleton]; omega), Finset.sum_singleton]
  rcases (by omega : l ≤ n - 3 ∨ l = n - 2 ∨ l = n - 1 ∨ l = n ∨ l = n + 1 ∨ l = n + 2 ∨
    n + 3 ≤ l) with h | h | h | h | h | h | h <;>
  · simp (disch := omega) only [cD, c0, c1, ite_eq_left, ite_eq_right]
    norm_num

/-- **The symmetric line is a symmetric complex.** `T λ = λ` and `∂ λ = 0`. -/
theorem symLine.str_T_and_cycle :
    (StructureCx.T symLine).f 1 symLine.str = symLine.str ∧
      (StructureCx symLine).d 1 0 symLine.str = 0 := by
  constructor
  · funext x
    obtain ⟨⟨p, q⟩, h⟩ := x
    rw [StructureCx.T_apply]
    by_cases hp : p = 0 ∨ p = 1
    · have hpq : p * q = 0 := by rcases hp with rfl | rfl <;> omega
      rw [hpq, Int.negOnePow_zero, one_smul]
      simp only [eqToHom_refl, Category.comp_id]
      refine Bounded.hom_ext fun m n => ?_
      rw [Bounded.dualHom_apply, symLine.str_apply, symLine.str_apply]
      change FreeQ.ofMatrix (fun _ _ => if q = 0 then (if n = m ∨ n = m + 1 then (1 / 2 : ℚ)
          else 0) else (if n + 1 = m ∨ n = m then 1 / 2 else 0)) =
        FreeQ.ofMatrix fun _ _ => if p = 0 then (if m = n ∨ m = n + 1 then 1 / 2 else 0)
          else (if m + 1 = n ∨ m = n then 1 / 2 else 0)
      congr 1
      funext _ _
      rcases hp with rfl | rfl
      · obtain rfl : q = 1 := by omega
        simp only [one_ne_zero, ite_false, ite_true]
        congr 1
        exact propext (by omega)
      · obtain rfl : q = 0 := by omega
        simp only [one_ne_zero, ite_false, ite_true]
        congr 1
        exact propext (by omega)
    · exact hom_ext_empty _ _ fun _ _ => Or.inl (isEmpty_X hp _)
  · funext x
    obtain ⟨⟨p, q⟩, h⟩ := x
    by_cases hpq : p = 0 ∧ q = 0
    · obtain ⟨rfl, rfl⟩ := hpq
      rw [StructureCx.d_apply symLine 1 0 symLine.str 0 0 h 1 1 rfl rfl, Int.negOnePow_zero,
        one_smul]
      have h1 : ∀ m n, (symLine.str ⟨(1, 0), rfl⟩).1 m n = FreeQ.ofMatrix fun _ _ => c1 m n :=
        fun m n => by rw [symLine.str_apply]; simp [c1]
      have h0 : ∀ m n, (symLine.str ⟨(0, 1), rfl⟩).1 m n = FreeQ.ofMatrix fun _ _ => c0 m n :=
        fun m n => by rw [symLine.str_apply]; simp [c0]
      have hd : ∀ m n, (symLine.d 1 0).1 m n = FreeQ.ofMatrix fun _ _ => cD m n :=
        fun m n => symLine.d_one_zero_apply m n
      have hdd : ∀ m n, (dualHom (symLine.d 1 0)).1 m n = FreeQ.ofMatrix fun _ _ => cD n m :=
        fun m n => by rw [Bounded.dualHom_apply, hd]; rfl
      refine Bounded.hom_ext fun l n => Matrix.ext fun i j => ?_
      rw [Bounded.add_apply]
      refine (congrArg₂ (· + ·)
        (comp_entry (M := dual (symLine.X 0)) (N := symLine.X 1) (P := symLine.X 0) _ _
          c1 cD h1 hd c1_eq_zero l n i j)
        (comp_entry (M := dual (symLine.X 0)) (N := dual (symLine.X 1)) (P := symLine.X 0) _ _
          (fun m n => cD n m) c0 hdd h0 cD'_eq_zero l n i j)).trans ?_
      change _ = (0 : ℚ)
      simp only [dim_one, dim_one', one_mul, ← Finset.sum_add_distrib]
      exact cycle_coef l n
    · refine hom_ext_empty _ _ fun _ n => ?_
      by_cases hp : p = 0 ∨ p = 1
      · exact Or.inr (isEmpty_X (r := q) (by omega) n)
      · exact Or.inl (isEmpty_X hp _)

end HSP
