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
import HilbertSmithPaper.ChainModels.Grid.Model.TensorLabel

/-!
# Propagation bounds for the based product and tensor maps

Label the basis of `C ⊗ E` by combining labels on `C` and `E` with a map that is `1`-Lipschitz for
the max distance. Then the product of structures, the product of duality maps, the tensor and the
dual tensor of graded maps have propagation at most the larger of the bounds for their factors.

## Proof

Every summand of these maps is a block projection, transports, a Kronecker product of factor
blocks and a block inclusion, up to sign. Block projections, inclusions and transports have
propagation `0`; a Kronecker product has at most the larger factor propagation, because the
combining map is `1`-Lipschitz; composites add propagations, and sums and signs do not increase
them.

## Encoding

`prop_productMaps` (the declaration of the article) is the conjunction of the four bounds, in the
order: product of structures, product of duality maps, tensor, dual tensor.
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

omit [MetricSpace X] [MetricSpace Y] [MetricSpace Z] in
private lemma tensorLabel_sigma (lC : ∀ r, Fin (C.X r).dim → X) (lE : ∀ r, Fin (E.X r).dim → Y)
    (c : X → Y → Z) (r : ℤ) (p : Fin (r.toNat + 1)) (b : Fin (tensorSummandDim C E r p)) :
    tensorLabel hE lC lE c r (finSigmaFinEquiv ⟨p, b⟩) =
      c (lC (p : ℕ) (finProdFinEquiv.symm b).1) (lE (r - (p : ℕ)) (finProdFinEquiv.symm b).2) := by
  unfold tensorLabel
  rw [Equiv.symm_apply_apply]

omit [MetricSpace X] [MetricSpace Y] [MetricSpace Z] in
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


/-- *Propagation bounds for the based product and tensor maps.* For labels on `C ⊗ E` combined
from labels on `C` and `E` by a map that is `1`-Lipschitz for the max distance, the product of
structures, the product of duality maps, the tensor and the dual tensor of graded maps have
propagation at most the larger of the bounds for their factors. -/
theorem prop_productMaps (lC : ∀ r, Fin (C.X r).dim → X) (lE : ∀ r, Fin (E.X r).dim → Y)
    (c : X → Y → Z) (hc : ∀ x x' y y', nndist (c x y) (c x' y') ≤ max (nndist x x') (nndist y y')) :
    (∀ (m m' k : ℤ) (hk : m + m' = k) (φ : (StructureCx C).X m) (θ : (StructureCx E).X m')
      (εC εE : ℝ≥0), (∀ x, prop (lC x.1.2) (lC x.1.1) (toMatrix (φ x)) ≤ εC) →
      (∀ x, prop (lE x.1.2) (lE x.1.1) (toMatrix (θ x)) ≤ εE) → ∀ x,
      prop (tensorLabel hE lC lE c x.1.2) (tensorLabel hE lC lE c x.1.1)
        (toMatrix (basedStrProd C E hE m m' k hk φ θ x)) ≤ max εC εE) ∧
    (∀ (m m' k : ℤ) (hk : m + m' = k) (f : ∀ r, C.X r ⟶ dual (C.X (m - r)))
      (g : ∀ r, E.X r ⟶ dual (E.X (m' - r))) (εC εE : ℝ≥0),
      (∀ r, prop (lC r) (lC (m - r)) (toMatrix (f r)) ≤ εC) →
      (∀ r, prop (lE r) (lE (m' - r)) (toMatrix (g r)) ≤ εE) → ∀ r,
      prop (tensorLabel hE lC lE c r) (tensorLabel hE lC lE c (k - r))
        (toMatrix (basedDualProd C E hE m m' k hk f g r)) ≤ max εC εE) ∧
    (∀ (d e : ℤ) (f : ∀ r, C.X r ⟶ C.X (r + d)) (g : ∀ r, E.X r ⟶ E.X (r + e)) (εC εE : ℝ≥0),
      (∀ r, prop (lC r) (lC (r + d)) (toMatrix (f r)) ≤ εC) →
      (∀ r, prop (lE r) (lE (r + e)) (toMatrix (g r)) ≤ εE) → ∀ r,
      prop (tensorLabel hE lC lE c r) (tensorLabel hE lC lE c (r + (d + e)))
        (toMatrix (basedTensorHom hE hE d e f g r)) ≤ max εC εE) ∧
    (∀ (m m' k : ℤ) (hk : m + m' = k) (d e : ℤ)
      (F : ∀ r, dual (C.X (m - r)) ⟶ dual (C.X (m - (r + d))))
      (G : ∀ r, dual (E.X (m' - r)) ⟶ dual (E.X (m' - (r + e)))) (εC εE : ℝ≥0),
      (∀ t, prop (lC (m - t)) (lC (m - (t + d))) (toMatrix (F t)) ≤ εC) →
      (∀ t, prop (lE (m' - t)) (lE (m' - (t + e))) (toMatrix (G t)) ≤ εE) → ∀ r,
      prop (tensorLabel hE lC lE c (k - r)) (tensorLabel hE lC lE c (k - (r + (d + e))))
        (toMatrix (basedDualTensorHom hE m m' k hk d e F G r)) ≤ max εC εE) :=
  ⟨prop_basedStrProd hE lC lE c hc, prop_basedDualProd hE lC lE c hc,
    prop_basedTensorHom hE lC lE c hc, prop_basedDualTensorHom hE lC lE c hc⟩

end Generic

end HSP.ChainModels
