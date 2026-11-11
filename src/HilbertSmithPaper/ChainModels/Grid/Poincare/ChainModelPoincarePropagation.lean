import Mathlib
import HilbertSmithPaper.Categories.Asymptotic.PropAdd
import HilbertSmithPaper.Categories.Asymptotic.PropMul
import HilbertSmithPaper.ChainModels.Grid.BasedComplexTensor
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.BasedStrProd
import HilbertSmithPaper.ChainModels.Grid.Tensor.StructureProducts.BasedDualProd
import HilbertSmithPaper.ChainModels.Grid.Tensor.BasedTensorHom
import HilbertSmithPaper.ChainModels.Grid.Tensor.BasedDualTensorHom
import HilbertSmithPaper.ChainModels.Grid.ChainModelDuality
import HilbertSmithPaper.ChainModels.Grid.Poincare.ChainModelH
import HilbertSmithPaper.ChainModels.Grid.Poincare.ChainModelHDual
import HilbertSmithPaper.ChainModels.Grid.Poincare.GridFactor.GridH
import HilbertSmithPaper.ChainModels.Grid.Poincare.GridFactor.GridHDual
import HilbertSmithPaper.ChainModels.Grid.Poincare.GridFactor.CircleA
import HilbertSmithPaper.ChainModels.Grid.Poincare.GridFactor.CircleADual
import HilbertSmithPaper.ChainModels.Grid.Poincare.GridFactor.IdDualDeg0
import HilbertSmithPaper.ChainModels.Grid.Poincare.GridFactor.GridDualMap
import HilbertSmithPaper.ChainModels.Grid.Model.ChainModelLabel
import HilbertSmithPaper.ChainModels.Grid.Cubical.GridCell
import HilbertSmithPaper.ChainModels.Grid.Cubical.GridCube
import HilbertSmithPaper.ChainModels.Grid.Model.TensorLabelGrid
import HilbertSmithPaper.ChainModels.Grid.Poincare.PropProductMaps


/-!
# The chain model is Poincaré: part 3

With cells and duals labelled at their centers, `φ_i`, `b_i`, `H_i`, `H'_i` have
`d_∞`-propagation at most `h_i = 4/k_i`.

## Proof

Every summand of a product of structures, a product of duality maps, a tensor or a dual tensor
of graded maps is a block projection, transports, a Kronecker product of factor blocks and a
block inclusion. With labels on the tensor product combined from labels on the factors by a map
that is `1`-Lipschitz for the max distance, block projections, inclusions and transports have
propagation `0`, and a Kronecker product has at most the larger factor propagation; sums and
signs do not increase it. The grid labels are combined by `Fin.snoc` (the sup metric of the
torus), and the chain-model labels forget the `CP²` factor. Induction over the circle factors
with circle duality (5) gives `2/k` for `φ`, `b` and `4/k` for `H`, `H'` (through `A = φ^s b`,
`A' = b φ^s`).
-/

open CategoryTheory
open scoped NNReal

namespace HSP.ChainModels

open FreeQ DualCat

section Generic

variable {X : Type*} [MetricSpace X]

/-- The propagation is at most `ε` when every nonzero entry is. -/
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

private lemma prop_comp_le {P Q R : FreeQ} (l : Fin P.dim → X) (l' : Fin Q.dim → X) (l'' : Fin
R.dim → X)
    (f : P ⟶ Q) (g : Q ⟶ R) :
    prop l l'' (toMatrix (f ≫ g)) ≤ prop l' l'' (toMatrix g) + prop l l' (toMatrix f) :=
  prop_mul_le l l' l'' (toMatrix f) (toMatrix g)

variable {C E : ChainComplex FreeQ ℤ} (hE : ∀ q < 0, (E.X q).dim = 0) {Y Z : Type*}

omit [MetricSpace X] in
private lemma tensorLabel_cast (lC : ∀ r, Fin (C.X r).dim → X) (lE : ∀ r, Fin (E.X r).dim → Y)
    (c : X → Y → Z) {r r' : ℤ} (h : r = r')
    (H : ((basedComplexTensor C E hE).X r).dim = ((basedComplexTensor C E hE).X r').dim)
    (a : Fin ((basedComplexTensor C E hE).X r).dim) :
    tensorLabel hE lC lE c r' (Fin.cast H a) = tensorLabel hE lC lE c r a := by
  subst h
  rfl

end Generic

section Grid

/-- The label of a basis cell of the grid complex: the center of its cube. -/
private noncomputable def gridLabel (k n : ℕ) (r : ℤ) (a : Fin ((gridComplex k n).X r).dim) :
Torus n :=
  (gridCell k n r a).center

private lemma nndist_snoc_le {n : ℕ} (x y : Torus n) (a b : AddCircle (4 : ℝ)) :
    nndist (Fin.snoc x a : Torus (n + 1)) (Fin.snoc y b) ≤ max (nndist x y) (nndist a b) :=
  tensorLabel_grid.1 n x y a b

private lemma gridLabel_succ (k n : ℕ) (r : ℤ) :
    gridLabel k (n + 1) r = tensorLabel (circleComplex_dim_neg k) (gridLabel k n) (circleLabel k)
      (fun x a => (Fin.snoc x a : Torus (n + 1))) r :=
  tensorLabel_grid.2.1 k n r

private lemma prop_torus_zero {B B' : Type*} [Fintype B] [Fintype B'] (l : B → Torus 0) (l' : B' →
Torus 0)
    (u : Matrix B' B ℚ) (ε : ℝ≥0) : prop l l' u ≤ ε :=
  prop_le_of_entries _ _ _ _ fun b' b _ => by
    rw [Subsingleton.elim (l' b') (l b), nndist_self]
    exact zero_le

private lemma le_nn {x : ℝ≥0} (c k : ℕ) (h : (x : ℝ) ≤ c / k) : x ≤ (c : ℝ≥0) / k := by
  rw [← NNReal.coe_le_coe]
  push_cast
  exact h

private lemma fam_label_cast {F : ℤ → FreeQ} (l : ∀ r, Fin (F r).dim → X) {r r' : ℤ} (h : r = r')
    (H : (F r).dim = (F r').dim) (i : Fin (F r).dim) : l r' (Fin.cast H i) = l r i := by
  subst h
  rfl

private lemma two_add_two_div (k : ℕ) : ((2 : ℕ) : ℝ≥0) / k + ((2 : ℕ) : ℝ≥0) / k =
((4 : ℕ) : ℝ≥0) / k := by
  rw [← add_div]
  norm_num

variable (k : ℕ)

private lemma circleA_prop (r : ℤ) :
    prop (circleLabel k r) (circleLabel k (r +
        0)) (toMatrix (circleA k r)) ≤ ((4 : ℕ) : ℝ≥0) / k := by
  refine (prop_comp_le _ (circleLabel k (1 - r)) _ _ _).trans ?_
  refine (add_le_add ((prop_comp_le _ (circleLabel k r) _ _ _).trans ?_)
    (le_nn 2 k ((circle_duality k).2.2.2.2.2.2.2.2.1 r))).trans (two_add_two_div k).le
  refine le_trans (add_le_add (prop_eqToHom _ _ _ fun i =>
    fam_label_cast (circleLabel k) (add_zero r).symm _ i).le
    (le_nn 2 k ((circle_duality k).2.2.2.2.2.2.1 ⟨(r, 1 - r), by ring⟩))) ?_
  rw [zero_add]

private lemma circleA'_prop (r : ℤ) :
    prop (circleLabel k (1 - r)) (circleLabel k (1 - (r +
        0))) (toMatrix (circleA' k r)) ≤ ((4 : ℕ) : ℝ≥0) / k := by
  refine (prop_comp_le _ (circleLabel k r) _ _ _).trans ?_
  refine (add_le_add ((prop_comp_le _ (circleLabel k (1 - r)) _ _ _).trans ?_)
    (le_nn 2 k ((circle_duality k).2.2.2.2.2.2.1 ⟨(r, 1 - r), by ring⟩))).trans
      (two_add_two_div k).le
  refine le_trans (add_le_add (prop_eqToHom _ _ _ fun i =>
    fam_label_cast (circleLabel k) (show 1 - r = 1 - (r + 0) by ring) _ i).le
    (le_nn 2 k ((circle_duality k).2.2.2.2.2.2.2.2.1 r))) ?_
  rw [zero_add]

private lemma two_le_four_div : ((2 : ℕ) : ℝ≥0) / k ≤ ((4 : ℕ) : ℝ≥0) / k := by
  gcongr
  norm_num

private lemma gridStructure_prop : ∀ (n : ℕ) (x : {x : ℤ × ℤ // x.1 + x.2 = (n : ℤ)}),
    prop (gridLabel k n x.1.2) (gridLabel k n x.1.1) (toMatrix (gridStructure k n x)) ≤
      ((2 : ℕ) : ℝ≥0) / k
  | 0, x => prop_torus_zero _ _ _ _
  | n + 1, x => by
    rw [gridLabel_succ, gridLabel_succ]
    exact ((prop_productMaps (circleComplex_dim_neg k) (gridLabel k n) (circleLabel k) _
      nndist_snoc_le).1 n 1 _ _ (gridStructure k n) (circlePhiSym k) _ _ (gridStructure_prop n)
      (fun x => le_nn 2 k ((circle_duality k).2.2.2.2.2.2.1 x)) x).trans (max_self _).le

private lemma gridDualMap_prop : ∀ (n : ℕ) (r : ℤ),
    prop (gridLabel k n r) (gridLabel k n ((n : ℤ) - r)) (toMatrix (gridDualMap k n r)) ≤
      ((2 : ℕ) : ℝ≥0) / k
  | 0, r => prop_torus_zero _ _ _ _
  | n + 1, r => by
    rw [gridLabel_succ, gridLabel_succ]
    exact ((prop_productMaps (circleComplex_dim_neg k) (gridLabel k n) (circleLabel k) _
      nndist_snoc_le).2.1 n 1 _ _ (gridDualMap k n) (circleB k) _ _ (gridDualMap_prop n)
      (fun r => le_nn 2 k ((circle_duality k).2.2.2.2.2.2.2.2.1 r)) r).trans (max_self _).le

private lemma gridH_prop : ∀ (n : ℕ) (r : ℤ),
    prop (gridLabel k n r) (gridLabel k n (r + 1)) (toMatrix (gridH k n r)) ≤ ((4 : ℕ) : ℝ≥0) / k
  | 0, r => prop_torus_zero _ _ _ _
  | n + 1, r => by
    rw [gridLabel_succ, gridLabel_succ]
    change prop _ _ (_ + _) ≤ _
    refine (prop_add_le _ _ _ _).trans (max_le ?_ ?_)
    · refine (prop_comp_le _ (tensorLabel (circleComplex_dim_neg k) (gridLabel k n) (circleLabel k)
        (fun x a => (Fin.snoc x a : Torus (n + 1))) (r + (1 + 0))) _ _ _).trans ?_
      refine le_trans (add_le_add (prop_eqToHom _ _ _ fun i =>
        tensorLabel_cast _ _ _ _ (show r + (1 + 0) = r + 1 by ring) _ i).le
        (((prop_productMaps (circleComplex_dim_neg k) (gridLabel k n) (circleLabel k) _
          nndist_snoc_le).2.2.1 1 0 (gridH k n) (circleA k) _ _ (gridH_prop n) (circleA_prop k)
            r).trans (max_self _).le)) ?_
      rw [zero_add]
    · refine (prop_comp_le _ (tensorLabel (circleComplex_dim_neg k) (gridLabel k n) (circleLabel k)
        (fun x a => (Fin.snoc x a : Torus (n + 1))) (r + (0 + 1))) _ _ _).trans ?_
      refine le_trans (add_le_add (prop_eqToHom _ _ _ fun i =>
        tensorLabel_cast _ _ _ _ (show r + (0 + 1) = r + 1 by ring) _ i).le
        (((prop_productMaps (circleComplex_dim_neg k) (gridLabel k n) (circleLabel k) _
          nndist_snoc_le).2.2.1 0 1 (idDeg0 (gridComplex k n)) (circleK k) 0 (((2 : ℕ) : ℝ≥0) / k)
          (fun t => (prop_eqToHom _ _ _ fun i =>
            fam_label_cast (gridLabel k n) (add_zero t).symm _ i).le)
          (fun t => le_nn 2 k ((circle_duality k).2.2.2.2.2.2.2.2.2.1 t)) r).trans
            (max_le zero_le (two_le_four_div k)))) ?_
      rw [zero_add]

private lemma gridH'_prop : ∀ (n : ℕ) (r : ℤ),
    prop (gridLabel k n ((n : ℤ) - r)) (gridLabel k n ((n : ℤ) - (r +
        1))) (toMatrix (gridH' k n r)) ≤
      ((4 : ℕ) : ℝ≥0) / k
  | 0, r => prop_torus_zero _ _ _ _
  | n + 1, r => by
    rw [gridLabel_succ, gridLabel_succ]
    change prop _ _ (_ + _) ≤ _
    refine (prop_add_le _ _ _ _).trans (max_le ?_ ?_)
    · refine (prop_comp_le _ (tensorLabel (circleComplex_dim_neg k) (gridLabel k n) (circleLabel k)
        (fun x a => (Fin.snoc x a : Torus (n + 1))) (((n + 1 : ℕ) : ℤ) - (r + (1 +
            0)))) _ _ _).trans ?_
      refine le_trans (add_le_add (prop_eqToHom _ _ _ fun i =>
        tensorLabel_cast _ _ _ _ (show ((n + 1 : ℕ) : ℤ) - (r + (1 + 0)) =
            ((n + 1 : ℕ) : ℤ) - (r + 1)
          by ring) _ i).le
        (((prop_productMaps (circleComplex_dim_neg k) (gridLabel k n) (circleLabel k) _
          nndist_snoc_le).2.2.2 n 1 _ _ 1 0 (gridH' k n) (circleA' k) _ _ (gridH'_prop n)
            (circleA'_prop k) r).trans (max_self _).le)) ?_
      rw [zero_add]
    · refine (prop_comp_le _ (tensorLabel (circleComplex_dim_neg k) (gridLabel k n) (circleLabel k)
        (fun x a => (Fin.snoc x a : Torus (n + 1))) (((n + 1 : ℕ) : ℤ) - (r + (0 +
            1)))) _ _ _).trans ?_
      refine le_trans (add_le_add (prop_eqToHom _ _ _ fun i =>
        tensorLabel_cast _ _ _ _ (show ((n + 1 : ℕ) : ℤ) - (r + (0 + 1)) =
            ((n + 1 : ℕ) : ℤ) - (r + 1)
          by ring) _ i).le
        (((prop_productMaps (circleComplex_dim_neg k) (gridLabel k n) (circleLabel k) _
          nndist_snoc_le).2.2.2 n 1 _ _ 0 1 (idDualDeg0 (gridComplex k n) n) (circleK' k) 0
          (((2 : ℕ) : ℝ≥0) / k)
          (fun t => (prop_eqToHom _ _ _ fun i =>
            fam_label_cast (gridLabel k n) (show (n : ℤ) - t = n - (t + 0) by ring) _ i).le)
          (fun t => le_nn 2 k ((circle_duality k).2.2.2.2.2.2.2.2.2.2 t)) r).trans
            (max_le zero_le (two_le_four_div k)))) ?_
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

private lemma to_real_bound {x : ℝ≥0} {k : ℕ} (h : x ≤ ((4 : ℕ) : ℝ≥0) / k) : (x : ℝ) ≤ 4 / k := by
  have := NNReal.coe_le_coe.mpr h
  push_cast at this
  exact this

/-- *The chain model is Poincaré*, part 3: With cells and duals labelled at their centers, `φ_i`,
`b_i`, `H_i`, `H'_i` have `d_∞`-propagation at most `h_i = 4/k_i`. -/
theorem chainModel_poincare_propagation (A : LocalDatum p n D ρplus) (i : ℕ) :
    ((∀ x, (prop (chainModelLabel A i x.1.2) (chainModelLabel A i x.1.1)
          ((chainModelDuality A i).φ x) : ℝ) ≤ 4 / meshSequence A i) ∧
      (∀ r, (prop (chainModelLabel A i r) (chainModelLabel A i ((n + 4 : ℕ) - r))
          ((chainModelDuality A i).b r) : ℝ) ≤ 4 / meshSequence A i) ∧
      (∀ r, (prop (chainModelLabel A i r) (chainModelLabel A i (r + 1)) (chainModelH A i r) : ℝ) ≤
        4 / meshSequence A i) ∧
      (∀ r, (prop (chainModelLabel A i ((n + 4 : ℕ) - r))
          (chainModelLabel A i ((n + 4 : ℕ) - (r + 1))) (chainModelH' A i r) : ℝ) ≤
        4 / meshSequence A i)) := by
  set K := meshSequence A i
  have PM := prop_productMaps cp2Complex_dim_neg (gridLabel K n) (fun _ _ => (0 : ℝ))
    (fun x _ => x) (fun _ _ _ _ => le_max_left _ _)
  refine ⟨fun x => to_real_bound ?_, fun r => to_real_bound ?_, fun r => to_real_bound ?_,
    fun r => to_real_bound ?_⟩
  · rw [chainModelLabel_eq, chainModelLabel_eq]
    exact (PM.1 n 4 _ (by push_cast; ring) (gridStructure K n) cp2Structure
          _ 0
      (gridStructure_prop K n) (fun x => prop_const_zero _) x).trans
        (max_le (two_le_four_div K) zero_le)
  · rw [chainModelLabel_eq, chainModelLabel_eq]
    exact (PM.2.1 n 4 _ (by push_cast; ring) (gridDualMap K n) cp2Inverse.f _ 0
      (gridDualMap_prop K n) (fun r => prop_const_zero _) r).trans
        (max_le (two_le_four_div K) zero_le)
  · rw [chainModelLabel_eq, chainModelLabel_eq]
    refine (prop_comp_le _ (tensorLabel cp2Complex_dim_neg (gridLabel K n) (fun _ _ => (0 : ℝ))
      (fun x _ => x) (r + (1 + 0))) _ _ _).trans ?_
    refine le_trans (add_le_add (prop_eqToHom _ _ _ fun i =>
      tensorLabel_cast _ _ _ _ (show r + (1 + 0) = r + 1 by ring) _ i).le
      ((PM.2.2.1 1 0 (gridH K n) (idDeg0 cp2Complex) _ 0 (gridH_prop K n)
        (fun r => prop_const_zero _) r).trans (max_le le_rfl zero_le))) ?_
    rw [zero_add]
  · rw [chainModelLabel_eq, chainModelLabel_eq]
    refine (prop_comp_le _ (tensorLabel cp2Complex_dim_neg (gridLabel K n) (fun _ _ => (0 : ℝ))
      (fun x _ => x) (((n + 4 : ℕ) : ℤ) - (r + (1 + 0)))) _ _ _).trans ?_
    refine le_trans (add_le_add (prop_eqToHom _ _ _ fun i =>
      tensorLabel_cast _ _ _ _ (show ((n + 4 : ℕ) : ℤ) - (r + (1 + 0)) = ((n + 4 : ℕ) : ℤ) - (r + 1)
        by ring) _ i).le
      ((PM.2.2.2 n 4 _ (by push_cast; ring) 1 0 (gridH' K n)
        (idDualDeg0 cp2Complex 4) _ 0 (gridH'_prop K n) (fun r => prop_const_zero _) r).trans
          (max_le le_rfl zero_le))) ?_
    rw [zero_add]

end Model

end HSP.ChainModels
