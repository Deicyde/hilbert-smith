import Mathlib
import HilbertSmithPaper.Categories.Asymptotic.PropAdd
import HilbertSmithPaper.Categories.Asymptotic.PropMul
import HilbertSmithPaper.Categories.Asymptotic.PropSmul
import HilbertSmithPaper.Categories.Asymptotic.PropOne
import HilbertSmithPaper.ChainModels.Grid.BasedComplexTensor
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.BasedKron
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

/-- The propagation of a finite sum is at most the largest propagation of its terms. -/
private lemma prop_sum_le {B B' : Type*} [Fintype B] [Fintype B'] (l : B → X) (l' : B' → X) {ι :
Type*}
    (s : Finset ι) (u : ι → Matrix B' B ℚ) (ε : ℝ≥0) (h : ∀ i ∈ s, prop l l' (u i) ≤ ε) :
    prop l l' (∑ i ∈ s, u i) ≤ ε := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (prop_add_le _ _ _ _).trans (max_le (h a (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- A nonzero entry is at distance at most the propagation. -/
private lemma nndist_le_prop {B B' : Type*} [Fintype B] [Fintype B'] (l : B → X) (l' : B' → X)
    (u : Matrix B' B ℚ) {b' : B'} {b : B} (h : u b' b ≠ 0) : nndist (l' b') (l b) ≤ prop l l' u :=
        by
  unfold prop
  exact Finset.le_sup (f := fun q : B' × B => nndist (l' q.1) (l q.2))
    (Finset.mem_filter.2 ⟨Finset.mem_univ (b', b), h⟩)

/-- The propagation is at most `ε` when every nonzero entry is. -/
private lemma prop_le_of_entries {B B' : Type*} [Fintype B] [Fintype B'] (l : B → X) (l' : B' → X)
    (u : Matrix B' B ℚ) (ε : ℝ≥0) (h : ∀ b' b, u b' b ≠ 0 → nndist (l' b') (l b) ≤ ε) :
    prop l l' u ≤ ε :=
  Finset.sup_le fun q hq => h q.1 q.2 (Finset.mem_filter.1 hq).2

private lemma prop_blockProj {m : ℕ} (d : Fin m → ℕ) (p : Fin m) (l : Fin (∑ i, d i) → X)
    (lp : Fin (d p) → X) (h : ∀ b, lp b = l (finSigmaFinEquiv ⟨p, b⟩)) :
    prop l lp (toMatrix (blockProj d p)) = 0 := by
  refine le_antisymm (prop_le_of_entries _ _ _ _ fun b a hba => ?_) zero_le
  have hs : finSigmaFinEquiv.symm a = ⟨p, b⟩ := by
    by_contra hne
    exact hba (by simp [blockProj, hne])
  rw [h b, ← hs, Equiv.apply_symm_apply, nndist_self]

private lemma prop_blockInc {m : ℕ} (d : Fin m → ℕ) (p : Fin m) (l : Fin (∑ i, d i) → X)
    (lp : Fin (d p) → X) (h : ∀ b, lp b = l (finSigmaFinEquiv ⟨p, b⟩)) :
    prop lp l (toMatrix (blockInc d p)) = 0 := by
  refine le_antisymm (prop_le_of_entries _ _ _ _ fun a b hab => ?_) zero_le
  have hs : finSigmaFinEquiv.symm a = ⟨p, b⟩ := by
    by_contra hne
    exact hab (by simp [blockInc, hne])
  rw [h b, ← hs, Equiv.apply_symm_apply, nndist_self]

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

/-- The propagation of a Kronecker product, for labels combined by a map `c` that is
`1`-Lipschitz for the max distance. -/
private lemma prop_basedKron {Y Z : Type*} [MetricSpace Y] [MetricSpace Z] {P P' Q Q' : FreeQ}
    (f : P ⟶ P') (g : Q ⟶ Q') (lf : Fin P.dim → X) (lf' : Fin P'.dim → X) (lg : Fin Q.dim → Y)
    (lg' : Fin Q'.dim → Y) (c : X → Y → Z)
    (hc : ∀ x x' y y', nndist (c x y) (c x' y') ≤ max (nndist x x') (nndist y y')) :
    prop (fun i => c (lf (finProdFinEquiv.symm i).1) (lg (finProdFinEquiv.symm i).2))
      (fun i => c (lf' (finProdFinEquiv.symm i).1) (lg' (finProdFinEquiv.symm i).2))
      (toMatrix (basedKron f g)) ≤ max (prop lf lf' (toMatrix f)) (prop lg lg' (toMatrix g)) := by
  refine prop_le_of_entries _ _ _ _ fun i' i h => ?_
  have h' : toMatrix f (finProdFinEquiv.symm i').1 (finProdFinEquiv.symm i).1 *
      toMatrix g (finProdFinEquiv.symm i').2 (finProdFinEquiv.symm i).2 ≠ 0 := h
  have hf := left_ne_zero_of_mul h'
  have hg := right_ne_zero_of_mul h'
  exact (hc _ _ _ _).trans (max_le_max (nndist_le_prop _ _ _ hf) (nndist_le_prop _ _ _ hg))

private lemma prop_units_smul_le {P Q : FreeQ} (u : ℤˣ) (f : P ⟶ Q) (l : Fin P.dim → X) (l' : Fin
Q.dim → X) :
    prop l l' (toMatrix (u • f)) ≤ prop l l' (toMatrix f) := by
  refine prop_le_of_entries _ _ _ _ fun b' b h => nndist_le_prop _ _ _ fun h0 => h ?_
  change (u • toMatrix f) b' b = 0
  rw [Matrix.smul_apply, h0, smul_zero]

private noncomputable def tensorLabelS {C E : ChainComplex FreeQ ℤ} {Y Z : Type*}
    (lC : ∀ r, Fin (C.X r).dim → X) (lE : ∀ r, Fin (E.X r).dim → Y) (c : X → Y → Z) (r : ℤ)
    (s : (p : Fin (r.toNat + 1)) × Fin (tensorSummandDim C E r p)) : Z :=
  c (lC (s.1 : ℕ) (finProdFinEquiv.symm
      (s.2 : Fin ((C.X (s.1 : ℕ)).dim * (E.X (r - (s.1 : ℕ))).dim))).1)
    (lE (r - (s.1 : ℕ)) (finProdFinEquiv.symm
      (s.2 : Fin ((C.X (s.1 : ℕ)).dim * (E.X (r - (s.1 : ℕ))).dim))).2)

/-- Labels on a tensor product of based complexes from labels on the factors. -/
private noncomputable def tensorLabel {C E : ChainComplex FreeQ ℤ} (hE : ∀ q < 0, (E.X q).dim = 0)
    {Y Z : Type*} (lC : ∀ r, Fin (C.X r).dim → X) (lE : ∀ r, Fin (E.X r).dim → Y)
    (c : X → Y → Z) (r : ℤ) (a : Fin ((basedComplexTensor C E hE).X r).dim) : Z :=
  tensorLabelS lC lE c r (finSigmaFinEquiv.symm (a : Fin (∑ p, tensorSummandDim C E r p)))

private lemma prop_comp_le {P Q R : FreeQ} (l : Fin P.dim → X) (l' : Fin Q.dim → X) (l'' : Fin
R.dim → X)
    (f : P ⟶ Q) (g : Q ⟶ R) :
    prop l l'' (toMatrix (f ≫ g)) ≤ prop l' l'' (toMatrix g) + prop l l' (toMatrix f) :=
  prop_mul_le l l' l'' (toMatrix f) (toMatrix g)

private lemma prop_hom_sum_le {P Q : FreeQ} (l : Fin P.dim → X) (l' : Fin Q.dim → X) {ι : Type*}
    (s : Finset ι) (f : ι → (P ⟶ Q)) (ε : ℝ≥0) (h : ∀ i ∈ s, prop l l' (toMatrix (f i)) ≤ ε) :
    prop l l' (toMatrix (∑ i ∈ s, f i)) ≤ ε := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [zero_toMatrix]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, add_toMatrix]
    exact (prop_add_le _ _ _ _).trans (max_le (h a (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

variable {C E : ChainComplex FreeQ ℤ} (hE : ∀ q < 0, (E.X q).dim = 0) {Y Z : Type*}
  [MetricSpace Y] [MetricSpace Z]

private lemma tensorLabel_sigma (lC : ∀ r, Fin (C.X r).dim → X) (lE : ∀ r, Fin (E.X r).dim → Y)
    (c : X → Y → Z) (r : ℤ) (p : Fin (r.toNat + 1)) (b : Fin (tensorSummandDim C E r p)) :
    tensorLabel hE lC lE c r (finSigmaFinEquiv ⟨p, b⟩) =
      c (lC (p : ℕ) (finProdFinEquiv.symm b).1) (lE (r - (p : ℕ)) (finProdFinEquiv.symm b).2) := by
  unfold tensorLabel
  rw [Equiv.symm_apply_apply]
  rfl

private lemma label_cast (lC : ∀ r, Fin (C.X r).dim → X) (lE : ∀ r, Fin (E.X r).dim → Y)
    (c : X → Y → Z) {j j' u u' : ℤ} (hj : j = j') (hu : u = u')
    (H : (C.X j).dim * (E.X u).dim =
        (C.X j').dim * (E.X u').dim) (i : Fin ((C.X j).dim * (E.X u).dim)) :
    c (lC j' (finProdFinEquiv.symm (Fin.cast H i)).1) (lE u' (finProdFinEquiv.symm (Fin.cast H
        i)).2) =
      c (lC j (finProdFinEquiv.symm i).1) (lE u (finProdFinEquiv.symm i).2) := by
  subst hj hu
  rfl

private lemma prop_basedStrProd (lC : ∀ r, Fin (C.X r).dim → X) (lE : ∀ r, Fin (E.X r).dim → Y)
    (c : X → Y → Z) (hc : ∀ x x' y y', nndist (c x y) (c x' y') ≤ max (nndist x x') (nndist y y'))
    (m m' k : ℤ) (hk : m + m' = k) (φ : (StructureCx C).X m) (θ : (StructureCx E).X m')
    (εC εE : ℝ≥0) (hφ : ∀ x, prop (lC x.1.2) (lC x.1.1) (toMatrix (φ x)) ≤ εC)
    (hθ : ∀ x, prop (lE x.1.2) (lE x.1.1) (toMatrix (θ x)) ≤ εE) (x) :
    prop (tensorLabel hE lC lE c x.1.2) (tensorLabel hE lC lE c x.1.1)
      (toMatrix (basedStrProd C E hE m m' k hk φ θ x)) ≤ max εC εE := by
  refine prop_hom_sum_le _ _ _ _ _ fun p _ => prop_hom_sum_le _ _ _ _ _ fun p' _ => ?_
  by_cases h : ((p' : ℕ) : ℤ) = m - (p : ℕ)
  · have h' : (((p' : ℕ) : ℤ) = m - (p : ℕ)) = True := eq_true h
    simp only [h', ↓reduceDIte]
    refine (prop_units_smul_le _ _ _ _).trans ?_
    refine (prop_comp_le _ (fun b => tensorLabel hE lC lE c x.1.2 (finSigmaFinEquiv ⟨p',
        b⟩)) _ _ _).trans ?_
    refine le_trans (add_le_add le_rfl (prop_blockProj _ _ _ _ fun _ => rfl).le) ?_
    rw [add_zero]
    refine (prop_comp_le _ (fun i => c (lC (m - (p : ℕ)) (finProdFinEquiv.symm i).1)
      (lE (m' - (x.1.1 - (p : ℕ))) (finProdFinEquiv.symm i).2)) _ _ _).trans ?_
    refine le_trans (add_le_add le_rfl (prop_eqToHom _ _ _ fun i =>
      (label_cast lC lE c (by omega) (by have := x.2; omega) _ i).trans
        (tensorLabel_sigma hE lC lE c _ _ _).symm).le) ?_
    rw [add_zero]
    refine (prop_comp_le _ (fun b => tensorLabel hE lC lE c x.1.1 (finSigmaFinEquiv ⟨p,
        b⟩)) _ _ _).trans ?_
    refine le_trans (add_le_add (prop_blockInc _ _ _ _ fun _ => rfl).le le_rfl) ?_
    rw [zero_add]
    have hL : (fun b => tensorLabel hE lC lE c x.1.1 (finSigmaFinEquiv ⟨p, b⟩)) =
        fun i => c (lC (p : ℕ) (finProdFinEquiv.symm i).1)
          (lE (x.1.1 - (p : ℕ)) (finProdFinEquiv.symm i).2) :=
      funext fun b => tensorLabel_sigma hE lC lE c _ _ _
    rw [hL]
    exact (prop_basedKron (φ ⟨(((p : ℕ) : ℤ), m - (p : ℕ)), by ring⟩)
      (θ ⟨(x.1.1 - (p : ℕ), m' - (x.1.1 - (p : ℕ))), by ring⟩) (lC (m - (p : ℕ))) (lC (p : ℕ))
      (lE (m' - (x.1.1 - (p : ℕ)))) (lE (x.1.1 - (p : ℕ))) c hc).trans
      (max_le_max (hφ ⟨(((p : ℕ) : ℤ), m - (p : ℕ)), by ring⟩)
        (hθ ⟨(x.1.1 - (p : ℕ), m' - (x.1.1 - (p : ℕ))), by ring⟩))
  · simp only [h, ↓reduceDIte, zero_toMatrix, prop_zero]
    exact zero_le

private lemma tensorLabel_cast (lC : ∀ r, Fin (C.X r).dim → X) (lE : ∀ r, Fin (E.X r).dim → Y)
    (c : X → Y → Z) {r r' : ℤ} (h : r = r')
    (H : ((basedComplexTensor C E hE).X r).dim = ((basedComplexTensor C E hE).X r').dim)
    (a : Fin ((basedComplexTensor C E hE).X r).dim) :
    tensorLabel hE lC lE c r' (Fin.cast H a) = tensorLabel hE lC lE c r a := by
  subst h
  rfl

private lemma prop_basedDualProd (lC : ∀ r, Fin (C.X r).dim → X) (lE : ∀ r, Fin (E.X r).dim → Y)
    (c : X → Y → Z) (hc : ∀ x x' y y', nndist (c x y) (c x' y') ≤ max (nndist x x') (nndist y y'))
    (m m' k : ℤ) (hk : m + m' = k) (f : ∀ r, C.X r ⟶ dual (C.X (m - r)))
    (g : ∀ r, E.X r ⟶ dual (E.X (m' - r))) (εC εE : ℝ≥0)
    (hf : ∀ r, prop (lC r) (lC (m - r)) (toMatrix (f r)) ≤ εC)
    (hg : ∀ r, prop (lE r) (lE (m' - r)) (toMatrix (g r)) ≤ εE) (r : ℤ) :
    prop (tensorLabel hE lC lE c r) (tensorLabel hE lC lE c (k - r))
      (toMatrix (basedDualProd C E hE m m' k hk f g r)) ≤ max εC εE := by
  refine prop_hom_sum_le _ _ _ _ _ fun a _ => prop_hom_sum_le _ _ _ _ _ fun a' _ => ?_
  by_cases h : ((a' : ℕ) : ℤ) = m - (a : ℕ)
  · have h' : (((a' : ℕ) : ℤ) = m - (a : ℕ)) = True := eq_true h
    simp only [h', ↓reduceDIte]
    refine (prop_units_smul_le _ _ _ _).trans ?_
    refine (prop_comp_le _ (fun b => tensorLabel hE lC lE c r (finSigmaFinEquiv ⟨a,
        b⟩)) _ _ _).trans ?_
    refine le_trans (add_le_add le_rfl (prop_blockProj (tensorSummandDim C E r) a
      (tensorLabel hE lC lE c r) _ fun _ => rfl).le) ?_
    rw [add_zero]
    have hL : (fun b => tensorLabel hE lC lE c r (finSigmaFinEquiv ⟨a, b⟩)) =
        fun i => c (lC (a : ℕ) (finProdFinEquiv.symm i).1) (lE (r - (a : ℕ)) (finProdFinEquiv.symm
            i).2) :=
      funext fun b => tensorLabel_sigma hE lC lE c _ _ _
    rw [hL]
    refine (prop_comp_le _ (fun i => c (lC (m - (a : ℕ)) (finProdFinEquiv.symm i).1)
      (lE (m' - (r - (a : ℕ))) (finProdFinEquiv.symm i).2)) _ _ _).trans ?_
    refine (add_le_add ((prop_comp_le _
      (fun b => tensorLabel hE lC lE c (k - r) (finSigmaFinEquiv ⟨a', b⟩)) _ _ _).trans
      (add_le_add (prop_blockInc (tensorSummandDim C E (k - r)) a' (tensorLabel hE lC lE c (k - r))
        _ fun _ => rfl).le (prop_eqToHom _ _ _ fun i =>
        (tensorLabel_sigma hE lC lE c _ _ _).trans
          (label_cast lC lE c (by omega) (by omega) _ i)).le))
      ((prop_basedKron (f (a : ℕ)) (g (r - (a : ℕ))) (lC (a : ℕ))
        (lC (m - (a : ℕ))) (lE (r - (a : ℕ))) (lE (m' - (r - (a : ℕ)))) c hc).trans
          (max_le_max (hf _) (hg _)))).trans ?_
    simp
  · simp only [h, ↓reduceDIte, zero_toMatrix, prop_zero]
    exact zero_le

private lemma prop_basedTensorHom (lC : ∀ r, Fin (C.X r).dim → X) (lE : ∀ r, Fin (E.X r).dim → Y)
    (c : X → Y → Z) (hc : ∀ x x' y y', nndist (c x y) (c x' y') ≤ max (nndist x x') (nndist y y'))
    (d e : ℤ) (f : ∀ r, C.X r ⟶ C.X (r + d)) (g : ∀ r, E.X r ⟶ E.X (r + e)) (εC εE : ℝ≥0)
    (hf : ∀ r, prop (lC r) (lC (r + d)) (toMatrix (f r)) ≤ εC)
    (hg : ∀ r, prop (lE r) (lE (r + e)) (toMatrix (g r)) ≤ εE) (r : ℤ) :
    prop (tensorLabel hE lC lE c r) (tensorLabel hE lC lE c (r + (d + e)))
      (toMatrix (basedTensorHom hE hE d e f g r)) ≤ max εC εE := by
  refine prop_hom_sum_le _ _ _ _ _ fun a _ => prop_hom_sum_le _ _ _ _ _ fun a' _ => ?_
  by_cases h : ((a' : ℕ) : ℤ) = (a : ℕ) + d
  · have h' : (((a' : ℕ) : ℤ) = (a : ℕ) + d) = True := eq_true h
    simp only [h', ↓reduceDIte]
    refine (prop_units_smul_le _ _ _ _).trans ?_
    refine (prop_comp_le _ (fun b => tensorLabel hE lC lE c r (finSigmaFinEquiv ⟨a,
        b⟩)) _ _ _).trans ?_
    refine le_trans (add_le_add le_rfl (prop_blockProj (tensorSummandDim C E r) a
      (tensorLabel hE lC lE c r) _ fun _ => rfl).le) ?_
    rw [add_zero]
    have hL : (fun b => tensorLabel hE lC lE c r (finSigmaFinEquiv ⟨a, b⟩)) =
        fun i => c (lC (a : ℕ) (finProdFinEquiv.symm i).1) (lE (r - (a : ℕ)) (finProdFinEquiv.symm
            i).2) :=
      funext fun b => tensorLabel_sigma hE lC lE c _ _ _
    rw [hL]
    refine (prop_comp_le _ (fun i => c (lC ((a : ℕ) + d) (finProdFinEquiv.symm i).1)
      (lE (r - (a : ℕ) + e) (finProdFinEquiv.symm i).2)) _ _ _).trans ?_
    refine (add_le_add ((prop_comp_le _
      (fun b => tensorLabel hE lC lE c (r + (d + e)) (finSigmaFinEquiv ⟨a', b⟩)) _ _ _).trans
      (add_le_add (prop_blockInc (tensorSummandDim C E (r + (d + e))) a'
        (tensorLabel hE lC lE c (r + (d + e))) _ fun _ => rfl).le (prop_eqToHom _ _ _ fun i =>
        (tensorLabel_sigma hE lC lE c _ _ _).trans
          (label_cast lC lE c (by omega) (by omega) _ i)).le))
      ((prop_basedKron (f (a : ℕ)) (g (r - (a : ℕ))) (lC (a : ℕ))
        (lC ((a : ℕ) + d)) (lE (r - (a : ℕ))) (lE (r - (a : ℕ) + e)) c hc).trans
          (max_le_max (hf _) (hg _)))).trans ?_
    simp
  · simp only [h, ↓reduceDIte, zero_toMatrix, prop_zero]
    exact zero_le

private lemma prop_basedDualTensorHom (lC : ∀ r, Fin (C.X r).dim → X) (lE : ∀ r,
Fin (E.X r).dim → Y)
    (c : X → Y → Z) (hc : ∀ x x' y y', nndist (c x y) (c x' y') ≤ max (nndist x x') (nndist y y'))
    (m m' k : ℤ) (hk : m + m' = k) (d e : ℤ)
    (F : ∀ r, dual (C.X (m - r)) ⟶ dual (C.X (m - (r + d))))
    (G : ∀ r, dual (E.X (m' - r)) ⟶ dual (E.X (m' - (r + e)))) (εC εE : ℝ≥0)
    (hF : ∀ t, prop (lC (m - t)) (lC (m - (t + d))) (toMatrix (F t)) ≤ εC)
    (hG : ∀ t, prop (lE (m' - t)) (lE (m' - (t + e))) (toMatrix (G t)) ≤ εE) (r : ℤ) :
    prop (tensorLabel hE lC lE c (k - r)) (tensorLabel hE lC lE c (k - (r + (d + e))))
      (toMatrix (basedDualTensorHom hE m m' k hk d e F G r)) ≤ max εC εE := by
  refine prop_hom_sum_le _ _ _ _ _ fun p _ => prop_hom_sum_le _ _ _ _ _ fun p' _ => ?_
  by_cases h : ((p' : ℕ) : ℤ) = (p : ℕ) - d
  · have h' : (((p' : ℕ) : ℤ) = (p : ℕ) - d) = True := eq_true h
    simp only [h', ↓reduceDIte]
    refine (prop_units_smul_le _ _ _ _).trans ?_
    refine (prop_comp_le _ (fun b => tensorLabel hE lC lE c (k - r) (finSigmaFinEquiv ⟨p, b⟩)) _ _
      _).trans ?_
    refine le_trans (add_le_add le_rfl (prop_blockProj (tensorSummandDim C E (k - r)) p
      (tensorLabel hE lC lE c (k - r)) _ fun _ => rfl).le) ?_
    rw [add_zero]
    refine (prop_comp_le _ (fun i => c (lC (m - (m - (p : ℕ))) (finProdFinEquiv.symm i).1)
      (lE (m' - (r - (m - (p : ℕ)))) (finProdFinEquiv.symm i).2)) _ _ _).trans ?_
    refine le_trans (add_le_add le_rfl (prop_eqToHom _ _ _ fun i =>
      (label_cast lC lE c (by omega) (by omega) _ i).trans
        (tensorLabel_sigma hE lC lE c _ _ _).symm).le) ?_
    rw [add_zero]
    refine (prop_comp_le _ (fun i => c (lC (m - (m - (p : ℕ) + d)) (finProdFinEquiv.symm i).1)
      (lE (m' - (r - (m - (p : ℕ)) + e)) (finProdFinEquiv.symm i).2)) _ _ _).trans ?_
    refine (add_le_add ((prop_comp_le _
      (fun b => tensorLabel hE lC lE c (k - (r + (d + e))) (finSigmaFinEquiv ⟨p', b⟩)) _ _ _).trans
      (add_le_add (prop_blockInc (tensorSummandDim C E (k - (r + (d + e)))) p'
        (tensorLabel hE lC lE c (k - (r + (d + e)))) _ fun _ => rfl).le (prop_eqToHom _ _ _ fun i =>
        (tensorLabel_sigma hE lC lE c _ _ _).trans
          (label_cast lC lE c (by omega) (by omega) _ i)).le))
      ((prop_basedKron (F (m - (p : ℕ))) (G (r - (m - (p : ℕ)))) (lC (m - (m - (p : ℕ))))
        (lC (m - (m - (p : ℕ) + d))) (lE (m' - (r - (m - (p : ℕ)))))
          (lE (m' - (r - (m - (p : ℕ)) + e))) c hc).trans
          (max_le_max (hF _) (hG _)))).trans ?_
    simp
  · simp only [h, ↓reduceDIte, zero_toMatrix, prop_zero]
    exact zero_le

end Generic

section Grid

/-- The label of a basis cell of the grid complex: the center of its cube. -/
private noncomputable def gridLabel (k n : ℕ) (r : ℤ) (a : Fin ((gridComplex k n).X r).dim) :
Torus n :=
  (gridCell k n r a).center

private lemma nndist_snoc_le {n : ℕ} (x y : Torus n) (a b : AddCircle (4 : ℝ)) :
    nndist (Fin.snoc x a : Torus (n + 1)) (Fin.snoc y b) ≤ max (nndist x y) (nndist a b) := by
  refine (nndist_pi_le_iff).2 fun j => ?_
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp only [Fin.snoc_last]
    exact le_max_right _ _
  · simp only [Fin.snoc_castSucc]
    exact (nndist_le_pi_nndist x y j).trans (le_max_left _ _)

private lemma gridLabel_succ (k n : ℕ) (r : ℤ) :
    gridLabel k (n + 1) r = tensorLabel (circleComplex_dim_neg k) (gridLabel k n) (circleLabel k)
      (fun x a => (Fin.snoc x a : Torus (n + 1))) r := by
  funext a
  refine funext fun j => Fin.lastCases ?_ (fun j => ?_) j
  · simp only [gridLabel, gridCell, tensorLabel, tensorLabelS, GridCube.center, Fin.snoc_last,
      circleLabel]
  · simp only [gridLabel, gridCell, tensorLabel, tensorLabelS, GridCube.center, Fin.snoc_castSucc]

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
    exact (prop_basedStrProd (circleComplex_dim_neg k) (gridLabel k n) (circleLabel k) _
      nndist_snoc_le n 1 _ _ (gridStructure k n) (circlePhiSym k) _ _ (gridStructure_prop n)
      (fun x => le_nn 2 k ((circle_duality k).2.2.2.2.2.2.1 x)) x).trans (max_self _).le

private lemma gridDualMap_prop : ∀ (n : ℕ) (r : ℤ),
    prop (gridLabel k n r) (gridLabel k n ((n : ℤ) - r)) (toMatrix (gridDualMap k n r)) ≤
      ((2 : ℕ) : ℝ≥0) / k
  | 0, r => prop_torus_zero _ _ _ _
  | n + 1, r => by
    rw [gridLabel_succ, gridLabel_succ]
    exact (prop_basedDualProd (circleComplex_dim_neg k) (gridLabel k n) (circleLabel k) _
      nndist_snoc_le n 1 _ _ (gridDualMap k n) (circleB k) _ _ (gridDualMap_prop n)
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
        ((prop_basedTensorHom (circleComplex_dim_neg k) (gridLabel k n) (circleLabel k) _
          nndist_snoc_le 1 0 (gridH k n) (circleA k) _ _ (gridH_prop n) (circleA_prop k) r).trans
            (max_self _).le)) ?_
      rw [zero_add]
    · refine (prop_comp_le _ (tensorLabel (circleComplex_dim_neg k) (gridLabel k n) (circleLabel k)
        (fun x a => (Fin.snoc x a : Torus (n + 1))) (r + (0 + 1))) _ _ _).trans ?_
      refine le_trans (add_le_add (prop_eqToHom _ _ _ fun i =>
        tensorLabel_cast _ _ _ _ (show r + (0 + 1) = r + 1 by ring) _ i).le
        ((prop_basedTensorHom (circleComplex_dim_neg k) (gridLabel k n) (circleLabel k) _
          nndist_snoc_le 0 1 (idDeg0 (gridComplex k n)) (circleK k) 0 (((2 : ℕ) : ℝ≥0) / k)
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
        ((prop_basedDualTensorHom (circleComplex_dim_neg k) (gridLabel k n) (circleLabel k) _
          nndist_snoc_le n 1 _ _ 1 0 (gridH' k n) (circleA' k) _ _ (gridH'_prop n) (circleA'_prop k)
            r).trans (max_self _).le)) ?_
      rw [zero_add]
    · refine (prop_comp_le _ (tensorLabel (circleComplex_dim_neg k) (gridLabel k n) (circleLabel k)
        (fun x a => (Fin.snoc x a : Torus (n + 1))) (((n + 1 : ℕ) : ℤ) - (r + (0 +
            1)))) _ _ _).trans ?_
      refine le_trans (add_le_add (prop_eqToHom _ _ _ fun i =>
        tensorLabel_cast _ _ _ _ (show ((n + 1 : ℕ) : ℤ) - (r + (0 + 1)) =
            ((n + 1 : ℕ) : ℤ) - (r + 1)
          by ring) _ i).le
        ((prop_basedDualTensorHom (circleComplex_dim_neg k) (gridLabel k n) (circleLabel k) _
          nndist_snoc_le n 1 _ _ 0 1 (idDualDeg0 (gridComplex k n) n) (circleK' k) 0
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
      (fun _ _ => (0 : ℝ)) (fun x _ => x) r := by
  funext a
  rfl

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
  refine ⟨fun x => to_real_bound ?_, fun r => to_real_bound ?_, fun r => to_real_bound ?_,
    fun r => to_real_bound ?_⟩
  · rw [chainModelLabel_eq, chainModelLabel_eq]
    exact (prop_basedStrProd cp2Complex_dim_neg (gridLabel K n) (fun _ _ => (0 : ℝ)) (fun x _ => x)
      (fun _ _ _ _ => le_max_left _ _) n 4 _ (by push_cast; ring) (gridStructure K n) cp2Structure
          _ 0
      (gridStructure_prop K n) (fun x => prop_const_zero _) x).trans
        (max_le (two_le_four_div K) zero_le)
  · rw [chainModelLabel_eq, chainModelLabel_eq]
    exact (prop_basedDualProd cp2Complex_dim_neg (gridLabel K n) (fun _ _ => (0 : ℝ)) (fun x _ => x)
      (fun _ _ _ _ => le_max_left _ _) n 4 _ (by push_cast; ring) (gridDualMap K n) cp2Inverse.f _ 0
      (gridDualMap_prop K n) (fun r => prop_const_zero _) r).trans
        (max_le (two_le_four_div K) zero_le)
  · rw [chainModelLabel_eq, chainModelLabel_eq]
    refine (prop_comp_le _ (tensorLabel cp2Complex_dim_neg (gridLabel K n) (fun _ _ => (0 : ℝ))
      (fun x _ => x) (r + (1 + 0))) _ _ _).trans ?_
    refine le_trans (add_le_add (prop_eqToHom _ _ _ fun i =>
      tensorLabel_cast _ _ _ _ (show r + (1 + 0) = r + 1 by ring) _ i).le
      ((prop_basedTensorHom cp2Complex_dim_neg (gridLabel K n) (fun _ _ => (0 : ℝ)) (fun x _ => x)
        (fun _ _ _ _ => le_max_left _ _) 1 0 (gridH K n) (idDeg0 cp2Complex) _ 0 (gridH_prop K n)
        (fun r => prop_const_zero _) r).trans (max_le le_rfl zero_le))) ?_
    rw [zero_add]
  · rw [chainModelLabel_eq, chainModelLabel_eq]
    refine (prop_comp_le _ (tensorLabel cp2Complex_dim_neg (gridLabel K n) (fun _ _ => (0 : ℝ))
      (fun x _ => x) (((n + 4 : ℕ) : ℤ) - (r + (1 + 0)))) _ _ _).trans ?_
    refine le_trans (add_le_add (prop_eqToHom _ _ _ fun i =>
      tensorLabel_cast _ _ _ _ (show ((n + 4 : ℕ) : ℤ) - (r + (1 + 0)) = ((n + 4 : ℕ) : ℤ) - (r + 1)
        by ring) _ i).le
      ((prop_basedDualTensorHom cp2Complex_dim_neg (gridLabel K n) (fun _ _ => (0 : ℝ))
        (fun x _ => x) (fun _ _ _ _ => le_max_left _ _) n 4 _ (by push_cast; ring) 1 0 (gridH' K n)
        (idDualDeg0 cp2Complex 4) _ 0 (gridH'_prop K n) (fun r => prop_const_zero _) r).trans
          (max_le le_rfl zero_le))) ?_
    rw [zero_add]

end Model

end HSP.ChainModels
