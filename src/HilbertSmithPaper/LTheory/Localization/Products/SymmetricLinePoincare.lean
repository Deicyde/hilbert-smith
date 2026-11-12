import Mathlib
import HilbertSmithPaper.LTheory.Base.Pairs.SymmetricPoincareComplex
import HilbertSmithPaper.LTheory.Base.Complexes.CycleChainMapHomotopy
import HilbertSmithPaper.LTheory.Localization.Products.SymmetricLineCycle
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.ConstantFamilyComp

/-!
# The line is Poincaré

The duality map `λ_♮ : Λ^{1-*} ⟶ Λ` of the symmetric line is a chain homotopy equivalence in
`C_ℤ(ℚ)`, so `(Λ, λ)` is a strict `1`-dimensional symmetric Poincaré complex.

The cellular duality `c ∈ M(Λ)_1`, `c_0(e^*_{n+1/2}) = v_{n+1}` and `c_1(v_n^*) = e_{n+1/2}`, is a
cycle whose duality map is an isomorphism (componentwise, with inverses of propagation `1`), and
`λ - c = ∂(-½ h)` for `h_1(e^*_{n+1/2}) = e_{n+1/2}`. Hence `λ_♮ ≃ c_♮`
(`HSP.StructureCx.toHom_homotopy`), and `c_♮^{-1}` is a homotopy inverse of `λ_♮`. All identities
are checked on the constant matrices of the components (`HSP.constFamily_comp_entry`).
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

namespace SymLinePoincare

/-- Morphisms between objects of `C_ℤ(ℚ)` agree when every block has an empty side. -/
private lemma hom_ext_empty {M N : Bounded FreeQ} (f g : M ⟶ N)
    (h : ∀ m n, IsEmpty (Fin (N.X m).dim) ∨ IsEmpty (Fin (M.X n).dim)) : f = g :=
  Bounded.hom_ext fun m n => Matrix.ext fun i j => (h m n).elim (fun _ => isEmptyElim i)
    (fun _ => isEmptyElim j)

private lemma isEmpty_X {r : ℤ} (hr : ¬(r = 0 ∨ r = 1)) (n : ℤ) :
    IsEmpty (Fin ((symLine.X r).X n).dim) := by
  rw [symLine.X_X]
  simp only [hr, ite_false]
  infer_instance

private lemma dim_X {r : ℤ} (hr : r = 0 ∨ r = 1) (m : ℤ) : ((symLine.X r).X m).dim = 1 := by
  rw [symLine.X_X]
  simp [hr]

private lemma dim_dual {r : ℤ} (hr : r = 0 ∨ r = 1) (m : ℤ) :
    ((dual (symLine.X r)).X m).dim = 1 :=
  dim_X hr m

private lemma isZero_dual {X : Bounded FreeQ} (h : IsZero X) : IsZero (dual X) := by
  rw [IsZero.iff_id_eq_zero] at h ⊢
  rw [← dualHom_id, h, dualHom_zero]

/-- The coefficients of `d : Λ_1 ⟶ Λ_0`. -/
private def cD (m n : ℤ) : ℚ := if m = n + 1 then 1 else if m = n then -1 else 0

private lemma cD_eq_zero (m n : ℤ) (h : 1 < |m - n|) : cD m n = 0 := by
  rw [lt_abs] at h
  simp (disch := omega) only [cD, ite_eq_right]

/-- The coefficients of the cellular duality `c`: `c_0(e^*_{n+1/2}) = v_{n+1}` (`p = 0`) and
`c_1(v_n^*) = e_{n+1/2}` (otherwise). -/
private def cCoef (p m n : ℤ) : ℚ :=
  if p = 0 then (if m = n + 1 then 1 else 0) else (if m = n then 1 else 0)

private lemma cCoef_eq_zero (p m n : ℤ) (h : 1 < |m - n|) : cCoef p m n = 0 := by
  rw [lt_abs] at h
  unfold cCoef
  split_ifs <;> first | rfl | omega

/-- The cellular duality `c ∈ M(Λ)_1`. -/
private noncomputable def c : (StructureCx symLine).X 1 := fun x =>
  ⟨fun m n => FreeQ.ofMatrix fun _ _ => cCoef x.1.1 m n, ⟨1, fun m n h => by
    change (fun _ _ => cCoef x.1.1 m n : Matrix _ _ ℚ) = 0
    ext
    simp [cCoef_eq_zero x.1.1 m n (by exact_mod_cast h)]⟩⟩

/-- The coefficients of `-½ h`, `h_1(e^*_{n+1/2}) = e_{n+1/2}`. -/
private def xCoef (p m n : ℤ) : ℚ := if p = 1 ∧ m = n then -1 / 2 else 0

private lemma xCoef_eq_zero (p m n : ℤ) (h : 1 < |m - n|) : xCoef p m n = 0 := by
  rw [lt_abs] at h
  unfold xCoef
  split_ifs with h' <;> first | rfl | omega

/-- `-½ h ∈ M(Λ)_2`. -/
private noncomputable def X : (StructureCx symLine).X 2 := fun x =>
  ⟨fun m n => FreeQ.ofMatrix fun _ _ => xCoef x.1.1 m n, ⟨1, fun m n h => by
    change (fun _ _ => xCoef x.1.1 m n : Matrix _ _ ℚ) = 0
    ext
    simp [xCoef_eq_zero x.1.1 m n (by exact_mod_cast h)]⟩⟩

private lemma hd (m n : ℤ) : (symLine.d 1 0).1 m n = FreeQ.ofMatrix fun _ _ => cD m n :=
  symLine.d_one_zero_apply m n

private lemma hdd (m n : ℤ) :
    (dualHom (symLine.d 1 0)).1 m n = FreeQ.ofMatrix fun _ _ => cD n m := by
  rw [Bounded.dualHom_apply, hd]
  rfl

private lemma three (n : ℤ) (F : ℤ → ℚ) :
    ∑ m ∈ Finset.Icc (n - 1) (n + 1), F m = F (n - 1) + F n + F (n + 1) := by
  have hI : Finset.Icc (n - 1) (n + 1) = {n - 1, n, n + 1} := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [hI, Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
    Finset.sum_insert (by simp only [Finset.mem_singleton]; omega), Finset.sum_singleton,
    add_assoc]

private lemma hc : (StructureCx symLine).d 1 0 c = 0 := by
  funext x
  obtain ⟨⟨p, q⟩, h⟩ := x
  by_cases hpq : p = 0 ∧ q = 0
  · obtain ⟨rfl, rfl⟩ := hpq
    rw [StructureCx.d_apply symLine 1 0 c 0 0 h 1 1 rfl rfl, Int.negOnePow_zero, one_smul]
    refine Bounded.hom_ext fun l n => Matrix.ext fun i j => ?_
    rw [Bounded.add_apply]
    refine (congrArg₂ (· + ·)
      (constFamily_comp_entry (M := dual (symLine.X 0)) (N := symLine.X 1) (P := symLine.X 0)
        _ _ (cCoef 1) cD (fun _ _ => rfl) hd (cCoef_eq_zero 1) l n i j)
      (constFamily_comp_entry (M := dual (symLine.X 0)) (N := dual (symLine.X 1))
        (P := symLine.X 0) _ _ (fun m n => cD n m) (cCoef 0) hdd (fun _ _ => rfl)
        (fun m n hmn => cD_eq_zero n m (by rwa [abs_sub_comm])) l n i j)).trans ?_
    change _ = (0 : ℚ)
    simp only [dim_X (r := 1) (by omega), dim_dual (r := 1) (by omega), Nat.cast_one, one_mul]
    rw [three, three]
    rcases (by omega : l ≤ n - 2 ∨ l = n - 1 ∨ l = n ∨ l = n + 1 ∨ l = n + 2 ∨ n + 3 ≤ l)
      with h' | h' | h' | h' | h' | h' <;>
    · simp (disch := omega) only [cD, cCoef, ite_eq_left, ite_eq_right, ite_true]
      norm_num
  · refine hom_ext_empty _ _ fun _ n => ?_
    by_cases hp : p = 0 ∨ p = 1
    · exact Or.inr (isEmpty_X (r := q) (by omega) n)
    · exact Or.inl (isEmpty_X hp _)

private lemma sub_entry {M N : Bounded FreeQ} (f g : M ⟶ N) (l n : ℤ) (i : Fin (N.X l).dim)
    (j : Fin (M.X n).dim) :
    FreeQ.toMatrix ((f - g).1 l n) i j = FreeQ.toMatrix (f.1 l n) i j - FreeQ.toMatrix (g.1 l n) i j :=
  rfl

private lemma neg_entry {M N : Bounded FreeQ} (f : M ⟶ N) (l n : ℤ) (i : Fin (N.X l).dim)
    (j : Fin (M.X n).dim) :
    FreeQ.toMatrix ((-f).1 l n) i j = -FreeQ.toMatrix (f.1 l n) i j :=
  rfl

private lemma hX : (StructureCx symLine).d 2 1 X = symLine.str - c := by
  funext x
  obtain ⟨⟨p, q⟩, h⟩ := x
  change _ = symLine.str ⟨(p, q), h⟩ - c ⟨(p, q), h⟩
  by_cases hp0 : p = 0
  · subst hp0
    obtain rfl : q = 1 := by omega
    rw [StructureCx.d_apply symLine 2 1 X 0 1 h 1 2 rfl rfl, Int.negOnePow_zero, one_smul,
      hom_ext_empty (dualHom (symLine.d 2 1)) 0
        (fun _ _ => Or.inl (isEmpty_X (r := 2) (by omega) _)), zero_comp, add_zero]
    refine Bounded.hom_ext fun l n => Matrix.ext fun i j => ?_
    refine (constFamily_comp_entry (M := dual (symLine.X 1)) (N := symLine.X 1)
      (P := symLine.X 0) _ _ (xCoef 1) cD (fun _ _ => rfl) hd (xCoef_eq_zero 1) l n i j).trans ?_
    refine Eq.trans ?_ (sub_entry _ _ l n i j).symm
    rw [symLine.str_apply]
    change _ = (if (0 : ℤ) = 0 then (if l = n ∨ l = n + 1 then (1 / 2 : ℚ) else 0)
      else (if l + 1 = n ∨ l = n then 1 / 2 else 0)) - cCoef 0 l n
    simp only [dim_X (r := 1) (by omega), Nat.cast_one, one_mul]
    rw [three]
    rcases (by omega : l ≤ n - 2 ∨ l = n - 1 ∨ l = n ∨ l = n + 1 ∨ l = n + 2 ∨ n + 3 ≤ l)
      with h' | h' | h' | h' | h' | h' <;>
    · simp (disch := omega) only [cD, cCoef, xCoef, ite_eq_left, ite_eq_right, ite_true,
        true_and]
      norm_num
  by_cases hp1 : p = 1
  · subst hp1
    obtain rfl : q = 0 := by omega
    rw [StructureCx.d_apply symLine 2 1 X 1 0 h 2 1 rfl rfl, Int.negOnePow_one, Units.neg_smul,
      one_smul, hom_ext_empty (X ⟨(2, 0), _⟩) 0
        (fun _ _ => Or.inl (isEmpty_X (r := 2) (by omega) _)), zero_comp, zero_add]
    refine Bounded.hom_ext fun l n => Matrix.ext fun i j => ?_
    refine (neg_entry _ l n i j).trans ?_
    rw [constFamily_comp_entry (M := dual (symLine.X 0)) (N := dual (symLine.X 1))
      (P := symLine.X 1) _ _ (fun m n => cD n m) (xCoef 1) hdd (fun _ _ => rfl)
      (fun m n _ => cD_eq_zero n m (by rwa [abs_sub_comm])) l n i j]
    refine Eq.trans ?_ (sub_entry _ _ l n i j).symm
    rw [symLine.str_apply]
    change _ = (if (1 : ℤ) = 0 then (if l = n ∨ l = n + 1 then (1 / 2 : ℚ) else 0)
      else (if l + 1 = n ∨ l = n then 1 / 2 else 0)) - cCoef 1 l n
    simp only [dim_dual (r := 1) (by omega), Nat.cast_one, one_mul]
    rw [three]
    rcases (by omega : n ≤ l - 2 ∨ n = l - 1 ∨ n = l ∨ n = l + 1 ∨ n = l + 2 ∨ l + 3 ≤ n)
      with h' | h' | h' | h' | h' | h' <;>
    · simp (disch := omega) only [cD, cCoef, xCoef, ite_eq_left, ite_eq_right, ite_true,
        true_and, one_ne_zero, ite_false]
      norm_num
  · exact hom_ext_empty _ _ fun _ _ => Or.inl (isEmpty_X (r := p) (by omega) _)

private def gCoef (p m n : ℤ) : ℚ :=
  if p = 0 then (if m + 1 = n then 1 else 0) else (if m = n then 1 else 0)

private lemma gCoef_eq_zero (p m n : ℤ) (h : 1 < |m - n|) : gCoef p m n = 0 := by
  rw [lt_abs] at h
  unfold gCoef
  split_ifs <;> first | rfl | omega

/-- The inverse of `c_p : Λ_{1-p}^* ⟶ Λ_p`, for `p ∈ {0, 1}`. -/
private noncomputable def g (p : ℤ) : symLine.X p ⟶ dual (symLine.X (1 - p)) :=
  ⟨fun m n => FreeQ.ofMatrix fun _ _ => gCoef p m n, ⟨1, fun m n h => by
    change (fun _ _ => gCoef p m n : Matrix _ _ ℚ) = 0
    ext
    simp [gCoef_eq_zero p m n (by exact_mod_cast h)]⟩⟩

/-- The identity of an object of `C_ℤ(ℚ)` that is `ℚ` in every position. -/
private lemma id_apply {M : Bounded FreeQ} (hM : ∀ n, (M.X n).dim = 1) (l n : ℤ) :
    (𝟙 M : M ⟶ M).1 l n = FreeQ.ofMatrix fun _ _ => if l = n then 1 else 0 := by
  refine Matrix.ext fun i j => ?_
  by_cases h : l = n
  · subst h
    have hij : i = j := Fin.ext (by have hi := i.2; have hj := j.2; have h1 := hM l; omega)
    subst hij
    change (Bounded.diagF (M := M) (N := M) (fun n => 𝟙 (M.X n)) l l) i i = _
    rw [Bounded.diagF_self]
    change (1 : Matrix (Fin (M.X l).dim) (Fin (M.X l).dim) ℚ) i i = _
    simp
  · change (Bounded.diagF (M := M) (N := M) (fun n => 𝟙 (M.X n)) l n) i j = _
    rw [Bounded.diagF_ne _ h]
    simp [h]

private lemma isIso_c (r : ℤ) : IsIso ((StructureCx.toHom c hc).f r) := by
  rw [StructureCx.toHom_f]
  by_cases hr : r = 0 ∨ r = 1
  · refine ⟨⟨g r, ?_, ?_⟩⟩
    · refine Bounded.hom_ext fun l n => ?_
      rw [id_apply (fun n => dim_dual (r := 1 - r) (by omega) n)]
      refine Matrix.ext fun i j => (constFamily_comp_entry (M := dual (symLine.X (1 - r)))
        (N := symLine.X r) (P := dual (symLine.X (1 - r))) _ _ (cCoef r) (gCoef r)
        (fun _ _ => rfl) (fun _ _ => rfl) (cCoef_eq_zero r) l n i j).trans ?_
      change _ = if l = n then (1 : ℚ) else 0
      simp only [dim_X hr, Nat.cast_one, one_mul]
      rw [three]
      rcases hr with rfl | rfl <;>
      rcases (by omega : l ≤ n - 2 ∨ l = n - 1 ∨ l = n ∨ l = n + 1 ∨ l = n + 2 ∨ n + 3 ≤ l)
        with h' | h' | h' | h' | h' | h' <;>
      · simp (disch := omega) only [cCoef, gCoef, ite_eq_left, ite_eq_right, ite_true,
          one_ne_zero, ite_false]
        norm_num
    · refine Bounded.hom_ext fun l n => ?_
      rw [id_apply (fun n => dim_X hr n)]
      refine Matrix.ext fun i j => (constFamily_comp_entry (M := symLine.X r)
        (N := dual (symLine.X (1 - r))) (P := symLine.X r) _ _ (gCoef r) (cCoef r)
        (fun _ _ => rfl) (fun _ _ => rfl) (gCoef_eq_zero r) l n i j).trans ?_
      change _ = if l = n then (1 : ℚ) else 0
      simp only [dim_dual (r := 1 - r) (by omega), Nat.cast_one, one_mul]
      rw [three]
      rcases hr with rfl | rfl <;>
      rcases (by omega : l ≤ n - 2 ∨ l = n - 1 ∨ l = n ∨ l = n + 1 ∨ l = n + 2 ∨ n + 3 ≤ l)
        with h' | h' | h' | h' | h' | h' <;>
      · simp (disch := omega) only [cCoef, gCoef, ite_eq_left, ite_eq_right, ite_true,
          one_ne_zero, ite_false]
        norm_num
  · have hS : IsZero (dual (symLine.X (1 - r))) := isZero_dual (symLine.isZero_X (by omega))
    have hT : IsZero (symLine.X r) := symLine.isZero_X hr
    exact ⟨⟨0, hS.eq_of_src _ _, hT.eq_of_src _ _⟩⟩

end SymLinePoincare

open SymLinePoincare in
/-- **The line is Poincaré**: `λ_♮ : Λ^{1-*} ⟶ Λ` is a chain homotopy equivalence. -/
theorem symLine_poincare :
    ∃ e : HomotopyEquiv (dualCx symLine 1) symLine,
      e.hom = StructureCx.toHom symLine.str symLine.str_T_and_cycle.2 := by
  obtain ⟨H⟩ := StructureCx.toHom_homotopy symLine.str c symLine.str_T_and_cycle.2 hc X hX
  have : ∀ r, IsIso ((StructureCx.toHom c hc).f r) := isIso_c
  have := HomologicalComplex.Hom.isIso_of_components (StructureCx.toHom c hc)
  exact ⟨{ hom := StructureCx.toHom symLine.str symLine.str_T_and_cycle.2
           inv := inv (StructureCx.toHom c hc)
           homotopyHomInvId := (H.compRight _).trans (Homotopy.ofEq (IsIso.hom_inv_id _))
           homotopyInvHomId := (H.compLeft _).trans (Homotopy.ofEq (IsIso.inv_hom_id _)) },
    rfl⟩

end HSP
