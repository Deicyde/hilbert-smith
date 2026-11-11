import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Model.ChainModel
import HilbertSmithPaper.ChainModels.Grid.Model.ChainModelLabel
import HilbertSmithPaper.Categories.Asymptotic.Propagation
import HilbertSmithPaper.Categories.Asymptotic.PropAdd
import HilbertSmithPaper.Categories.Asymptotic.PropMul
import HilbertSmithPaper.ChainModels.Grid.Cubical.CircleComplex
import HilbertSmithPaper.ChainModels.Grid.Cubical.GridCell
import HilbertSmithPaper.ChainModels.Grid.Cubical.GridCube
import HilbertSmithPaper.ChainModels.Grid.CircleDuality
import HilbertSmithPaper.ChainModels.Grid.Tensor.TensorDifferential
import HilbertSmithPaper.ChainModels.Grid.Tensor.IdDeg0
import HilbertSmithPaper.ChainModels.Grid.Model.TensorLabel
import HilbertSmithPaper.ChainModels.Grid.Model.TensorLabelGrid
import HilbertSmithPaper.ChainModels.Grid.Poincare.PropProductMaps

/-!
# Propagation of the differential of the chain model

With cells of the chain model `D_i` labelled at the centers of their cubes, the differential has
`d_∞`-propagation at most `h_i / 2 = 2 / k_i`: the cells occurring in `d(c ⊗ e)` are `c' ⊗ e` with
`c'` a face of `c`, whose center differs from that of `c` by `2 / k_i` in one coordinate.

## Proof

The differential of a tensor product of based complexes is `d ⊗ 1 + 1 ⊗ d` up to transports. In
`S_k` the vertices `[w]`, `[w+1]` of the edge `e_w` sit at distance `2/k` from its center. By the
propagation bound for the tensor of graded maps, induction over the circle factors gives `2/k` for
the differential of `C(k)`, and then for `D_i = C(k_i) ⊗ P`, where `P` has labels forgotten.

## Encoding

`chainModel_d_propagation` (the declaration of the article) bounds the propagation of every
component `d r s` of the differential (it is `0` unless `s = r - 1`), with the torus labels
`chainModelLabel`.
-/

open CategoryTheory
open scoped NNReal

namespace HSP.ChainModels

open FreeQ

section Generic

variable {X : Type*} [MetricSpace X]

private lemma prop_le_of_entries {B B' : Type*} [Fintype B] [Fintype B'] (l : B → X) (l' : B' → X)
    (u : Matrix B' B ℚ) (ε : ℝ≥0) (h : ∀ b' b, u b' b ≠ 0 → nndist (l' b') (l b) ≤ ε) :
    prop l l' u ≤ ε :=
  Finset.sup_le fun q hq => h q.1 q.2 (Finset.mem_filter.1 hq).2

private lemma prop_eqToHom {Y Y' : FreeQ} (h : Y = Y') (l : Fin Y.dim → X) (l' : Fin Y'.dim → X)
    (hl : ∀ i, l' (Fin.cast (congrArg FreeQ.dim h) i) = l i) :
    prop l l' (toMatrix (eqToHom h)) = 0 := by
  subst h
  rw [eqToHom_refl, id_toMatrix]
  refine le_antisymm (prop_le_of_entries _ _ _ _ fun i' i hi => ?_) zero_le
  have hii : i' = i := by
    by_contra hne
    exact hi (Matrix.one_apply_ne hne)
  subst hii
  rw [← hl i', Fin.cast_eq_self, nndist_self]

private lemma prop_comp_le {P Q R : FreeQ} (l : Fin P.dim → X) (l' : Fin Q.dim → X)
    (l'' : Fin R.dim → X) (f : P ⟶ Q) (g : Q ⟶ R) :
    prop l l'' (toMatrix (f ≫ g)) ≤ prop l' l'' (toMatrix g) + prop l l' (toMatrix f) :=
  prop_mul_le l l' l'' (toMatrix f) (toMatrix g)

omit [MetricSpace X] in
private lemma fam_label_cast {F : ℤ → FreeQ} (l : ∀ r, Fin (F r).dim → X) {r r' : ℤ} (h : r = r')
    (H : (F r).dim = (F r').dim) (i : Fin (F r).dim) : l r' (Fin.cast H i) = l r i := by
  subst h
  rfl

omit [MetricSpace X] in
private lemma tensorLabel_cast {C E : ChainComplex FreeQ ℤ} (hE : ∀ q < 0, (E.X q).dim = 0)
    {Y Z : Type*} (lC : ∀ r, Fin (C.X r).dim → X) (lE : ∀ r, Fin (E.X r).dim → Y)
    (c : X → Y → Z) {r r' : ℤ} (h : r = r')
    (H : ((basedComplexTensor C E hE).X r).dim = ((basedComplexTensor C E hE).X r').dim)
    (a : Fin ((basedComplexTensor C E hE).X r).dim) :
    tensorLabel hE lC lE c r' (Fin.cast H a) = tensorLabel hE lC lE c r a := by
  subst h
  rfl

end Generic

section Circle

variable (k : ℕ)

private lemma dist_circle (hk : 0 < k) (x y : ℝ) (m : ℤ) (h : |x - y + 4 * m * k| ≤ 2) :
    dist (((x / k : ℝ)) : AddCircle (4 : ℝ)) ((y / k : ℝ) : AddCircle (4 : ℝ)) ≤ 2 / k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have e : (((x / k : ℝ)) - ((y / k : ℝ)) : AddCircle (4 : ℝ)) =
      (((x - y + 4 * m * k) / k : ℝ) : AddCircle (4 : ℝ)) := by
    rw [← AddCircle.coe_sub, QuotientAddGroup.eq_iff_sub_mem]
    refine AddSubgroup.mem_zmultiples_iff.2 ⟨-m, ?_⟩
    rw [zsmul_eq_mul]
    field_simp
    push_cast
    ring
  rw [dist_eq_norm, e]
  refine QuotientAddGroup.norm_mk_le_norm.trans ?_
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hk']
  exact div_le_div_of_nonneg_right h hk'.le

/-- The differential of `S_k` has propagation at most `2/k`. -/
private lemma circleD_prop (r s : ℤ) :
    prop (circleLabel k r) (circleLabel k s) (toMatrix ((circleComplex k).d r s)) ≤
      ((2 : ℕ) : ℝ≥0) / k := by
  by_cases hrs : r = 1 ∧ s = 0
  · obtain ⟨rfl, rfl⟩ := hrs
    rw [circleComplex_d]
    change prop (fun b : Fin k => circleLabel k 1 b) (fun a : Fin k => circleLabel k 0 a)
      (circleDiffMatrix k) ≤ _
    refine prop_le_of_entries _ _ _ _ fun a b hab => ?_
    have hb : (b : ℕ) < k := b.2
    have hk : 0 < k := lt_of_le_of_lt (Nat.zero_le _) hb
    rw [← NNReal.coe_le_coe, coe_nndist]
    push_cast
    change dist (((4 * ((a : ℕ) : ℝ) + 0) / k : ℝ) : AddCircle (4 : ℝ))
      (((4 * ((b : ℕ) : ℝ) + 2) / k : ℝ) : AddCircle (4 : ℝ)) ≤ 2 / k
    simp only [circleDiffMatrix, Matrix.of_apply] at hab
    split_ifs at hab with h1 h2 h2
    · simp at hab
    · by_cases hb1 : (b : ℕ) + 1 = k
      · rw [hb1, Nat.mod_self] at h1
        have ha : ((a : ℕ) : ℝ) = 0 := by exact_mod_cast h1
        have hbk : ((b : ℕ) : ℝ) + 1 = k := by exact_mod_cast hb1
        refine dist_circle k hk _ _ 1 ?_
        rw [abs_le]; constructor <;> push_cast <;> linarith
      · rw [Nat.mod_eq_of_lt (by omega)] at h1
        have ha : ((a : ℕ) : ℝ) = (b : ℕ) + 1 := by exact_mod_cast h1
        refine dist_circle k hk _ _ 0 ?_
        rw [abs_le]; constructor <;> push_cast <;> linarith
    · subst h2
      refine dist_circle k hk _ _ 0 ?_
      rw [abs_le]; constructor <;> push_cast <;> linarith
    · simp at hab
  · by_cases hsr : s + 1 = r
    · subst hsr
      have hs1 : s ≠ 0 := fun h => hrs ⟨by omega, h⟩
      have h : circleDim k (s + 1) = 0 ∨ circleDim k s = 0 := by
        rcases s with (_ | s) | s
        · exact absurd rfl hs1
        · exact Or.inl rfl
        · exact Or.inr rfl
      refine prop_le_of_entries _ _ _ _ fun a b _ => ?_
      have ha : (a : ℕ) < circleDim k s := a.2
      have hb : (b : ℕ) < circleDim k (s + 1) := b.2
      omega
    · rw [(circleComplex k).shape r s (by simp only [ComplexShape.down_Rel]; omega), zero_toMatrix,
        prop_zero]
      exact zero_le

end Circle

section Grid

/-- The label of a basis cell of the grid complex: the center of its cube. -/
private noncomputable def gridLabel (k n : ℕ) (r : ℤ) (a : Fin ((gridComplex k n).X r).dim) :
    Torus n :=
  (gridCell k n r a).center

private lemma gridLabel_succ (k n : ℕ) (r : ℤ) :
    gridLabel k (n + 1) r = tensorLabel (circleComplex_dim_neg k) (gridLabel k n) (circleLabel k)
      (fun x a => (Fin.snoc x a : Torus (n + 1))) r :=
  tensorLabel_grid.2.1 k n r

private lemma prop_torus_zero {B B' : Type*} [Fintype B] [Fintype B'] (l : B → Torus 0)
    (l' : B' → Torus 0) (u : Matrix B' B ℚ) (ε : ℝ≥0) : prop l l' u ≤ ε :=
  prop_le_of_entries _ _ _ _ fun b' b _ => by
    rw [Subsingleton.elim (l' b') (l b), nndist_self]
    exact zero_le

variable (k : ℕ)

/-- The differential of `C(k)` has propagation at most `2/k`. -/
private lemma gridD_prop : ∀ (n : ℕ) (r : ℤ),
    prop (gridLabel k n r) (gridLabel k n (r + -1)) (toMatrix ((gridComplex k n).d r (r + -1))) ≤
      ((2 : ℕ) : ℝ≥0) / k
  | 0, r => prop_torus_zero _ _ _ _
  | n + 1, r => by
    have PM := prop_productMaps (circleComplex_dim_neg k) (gridLabel k n) (circleLabel k)
      (fun x a => (Fin.snoc x a : Torus (n + 1))) (tensorLabel_grid.1 n)
    rw [gridLabel_succ, gridLabel_succ]
    change prop _ _ (toMatrix ((basedComplexTensor (gridComplex k n) (circleComplex k)
      (circleComplex_dim_neg k)).d r (r - 1))) ≤ _
    rw [basedComplexTensor_d_eq, add_toMatrix]
    refine (prop_add_le _ _ _ _).trans (max_le ?_ ?_)
    · refine (prop_comp_le _ (tensorLabel (circleComplex_dim_neg k) (gridLabel k n) (circleLabel k)
        (fun x a => (Fin.snoc x a : Torus (n + 1))) (r + (-1 + 0))) _ _ _).trans ?_
      refine le_trans (add_le_add (prop_eqToHom _ _ _ fun i =>
        tensorLabel_cast _ _ _ _ (show r + (-1 + 0) = r - 1 by ring) _ i).le
        ((PM.2.2.1 (-1) 0 (fun t => (gridComplex k n).d t (t + -1)) (idDeg0 (circleComplex k)) _ 0
          (gridD_prop n) (fun t => (prop_eqToHom _ _ _ fun i =>
            fam_label_cast (circleLabel k) (add_zero t).symm _ i).le) r).trans
          (max_le le_rfl zero_le))) ?_
      rw [zero_add]
    · refine (prop_comp_le _ (tensorLabel (circleComplex_dim_neg k) (gridLabel k n) (circleLabel k)
        (fun x a => (Fin.snoc x a : Torus (n + 1))) (r + (0 + -1))) _ _ _).trans ?_
      refine le_trans (add_le_add (prop_eqToHom _ _ _ fun i =>
        tensorLabel_cast _ _ _ _ (show r + (0 + -1) = r - 1 by ring) _ i).le
        ((PM.2.2.1 0 (-1) (idDeg0 (gridComplex k n)) (fun t => (circleComplex k).d t (t + -1)) 0 _
          (fun t => (prop_eqToHom _ _ _ fun i =>
            fam_label_cast (gridLabel k n) (add_zero t).symm _ i).le) (fun t => circleD_prop k t (t + -1)) r).trans
          (max_le zero_le le_rfl))) ?_
      rw [zero_add]

end Grid

section Model

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

private lemma chainModelLabel_eq (A : LocalDatum p n D ρplus) (i : ℕ) (r : ℤ) :
    chainModelLabel A i r = tensorLabel cp2Complex_dim_neg (gridLabel (meshSequence A i) n)
      (fun _ _ => (0 : ℝ)) (fun x _ => x) r :=
  tensorLabel_grid.2.2 p n D ρplus A i r

private lemma prop_const_zero {B B' : Type*} [Fintype B] [Fintype B'] (u : Matrix B' B ℚ) :
    prop (fun _ : B => (0 : ℝ)) (fun _ : B' => (0 : ℝ)) u ≤ 0 :=
  prop_le_of_entries _ _ _ _ fun _ _ _ => (nndist_self _).le

private lemma to_real_bound {x : ℝ≥0} {k : ℕ} (h : x ≤ ((2 : ℕ) : ℝ≥0) / k) : (x : ℝ) ≤ 2 / k := by
  have := NNReal.coe_le_coe.mpr h
  push_cast at this
  exact this

/-- **Propagation of the differential of the chain model.** Every component of the differential
of `D_i` has propagation at most `h_i / 2 = 2 / k_i` for the torus labels. -/
theorem chainModel_d_propagation (A : LocalDatum p n D ρplus) (i : ℕ) (r s : ℤ) :
    (prop (chainModelLabel A i r) (chainModelLabel A i s)
      (toMatrix ((chainModel A i).d r s)) : ℝ) ≤ 2 / meshSequence A i := by
  by_cases hrs : s = r + -1
  · subst hrs
    set K := meshSequence A i
    have PM := prop_productMaps cp2Complex_dim_neg (gridLabel K n) (fun _ _ => (0 : ℝ))
      (fun x _ => x) (fun _ _ _ _ => le_max_left _ _)
    refine to_real_bound ?_
    rw [chainModelLabel_eq, chainModelLabel_eq]
    change prop _ _ (toMatrix ((basedComplexTensor (gridComplex K n) cp2Complex
      cp2Complex_dim_neg).d r (r - 1))) ≤ _
    rw [basedComplexTensor_d_eq, add_toMatrix]
    refine (prop_add_le _ _ _ _).trans (max_le ?_ ?_)
    · refine (prop_comp_le _ (tensorLabel cp2Complex_dim_neg (gridLabel K n) (fun _ _ => (0 : ℝ))
        (fun x _ => x) (r + (-1 + 0))) _ _ _).trans ?_
      refine le_trans (add_le_add (prop_eqToHom _ _ _ fun i =>
        tensorLabel_cast _ _ _ _ (show r + (-1 + 0) = r - 1 by ring) _ i).le
        ((PM.2.2.1 (-1) 0 (fun t => (gridComplex K n).d t (t + -1)) (idDeg0 cp2Complex) _ 0
          (gridD_prop K n) (fun t => prop_const_zero _) r).trans (max_le le_rfl zero_le))) ?_
      rw [zero_add]
    · refine (prop_comp_le _ (tensorLabel cp2Complex_dim_neg (gridLabel K n) (fun _ _ => (0 : ℝ))
        (fun x _ => x) (r + (0 + -1))) _ _ _).trans ?_
      refine le_trans (add_le_add (prop_eqToHom _ _ _ fun i =>
        tensorLabel_cast _ _ _ _ (show r + (0 + -1) = r - 1 by ring) _ i).le
        ((PM.2.2.1 0 (-1) (idDeg0 (gridComplex K n)) (fun t => cp2Complex.d t (t + -1)) 0 0
          (fun t => (prop_eqToHom _ _ _ fun i =>
            fam_label_cast (gridLabel K n) (add_zero t).symm _ i).le)
          (fun t => prop_const_zero _) r).trans
            (max_le zero_le zero_le : max (0 : ℝ≥0) 0 ≤ ((2 : ℕ) : ℝ≥0) / K))) ?_
      rw [zero_add]
  · rw [(chainModel A i).shape r s (by simp only [ComplexShape.down_Rel]; omega), zero_toMatrix,
      prop_zero]
    positivity

end Model

end HSP.ChainModels
