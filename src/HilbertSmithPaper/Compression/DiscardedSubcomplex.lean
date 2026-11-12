import Mathlib
import HilbertSmithPaper.Compression.DiscardProjection

/-!
# The discarded cells form a subcomplex

With `pr_i` the based projection of `D_i` onto the span of the retained cells and `Q_i` the based
projection onto the span of the discarded cells, `pr_i d Q_i = 0` and `Q_i^* d^* pr_i^* = 0`.

## Encoding

* `Q_i = 1 - in_i pr_i` is `discardProj`; the duals `Q_i^*`, `d^*`, `pr_i^*` are transposes, so
  the second identity is `Q_iᵀ dᵀ pr_iᵀ = 0`.
* `pr_d_Q` (the declaration of the article) states both identities for the component
  `(chainModel _ i).d r s` of the differential, for all `r s` (it is `0` unless `s = r - 1`), so
  that callers can use any spelling of the target degree; and for every `i` (for `i < i₀`,
  `pr_i` has no rows).

## Proof

The private face lemma: a nonzero entry of the differential of `D_i` goes from a cell to a cell
whose closed cube lies in the first one's. It is proved for labellings of basis cells by sets that
are *monotone* (every nonzero entry of `d` decreases the label): the product labelling of a based
tensor product of monotone labellings is monotone (read off the blocks of the tensor
differential, which are Kronecker products), the circle complex is monotone for the realizations
of its cells, hence so is the grid complex by induction (the realization of a cube is a preimage
of a product), and `D_i = C(k_i) ⊗ P` is labelled by the cube times the one-point set. A
discarded cell's cube misses `K_t`, so a nonzero entry from it lands in a discarded cell, which is
`pr d Q = 0`.
-/

open CategoryTheory

namespace HSP.Compression

open HSP.ChainModels FreeQ
open scoped Matrix

section Face

/-- A labelling of the basis cells of `C` by sets is *monotone* if every nonzero entry of the
differential goes from a cell to a cell with smaller label. -/
private def LabelMono (C : ChainComplex FreeQ ℤ) {α : Type*} (L : ∀ r, Fin (C.X r).dim → Set α) : Prop :=
  ∀ r s a' a, toMatrix (C.d r s) a' a ≠ 0 → L s a' ⊆ L r a

private lemma eqToHom_entry {X Y : FreeQ} (h : X = Y) (i : Fin Y.dim) (j : Fin X.dim)
    (hne : toMatrix (eqToHom h) i j ≠ 0) : (i : ℕ) = j := by
  subst h
  by_contra hij
  exact hne (by simp [show i ≠ j from fun e => hij (congrArg _ e)])

private lemma label_congr (C : ChainComplex FreeQ ℤ) {α : Type*} (L : ∀ r, Fin (C.X r).dim → Set α)
    {r r' : ℤ} (h : r = r') (y : Fin (C.X r).dim) (y' : Fin (C.X r').dim) (hy : (y : ℕ) = y') :
    L r y = L r' y' := by
  subst h
  rw [Fin.ext hy]

private lemma basedKron_entry {X X' Y Y' : FreeQ} (f : X ⟶ X') (g : Y ⟶ Y') (i j) :
    toMatrix (basedKron f g) i j =
      toMatrix f (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1 *
        toMatrix g (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2 := rfl

private lemma toMatrix_sum_apply {X Y : FreeQ} {ι : Type*} (s : Finset ι) (f : ι → (X ⟶ Y)) (i j) :
    toMatrix (∑ k ∈ s, f k) i j = ∑ k ∈ s, toMatrix (f k) i j := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx, add_toMatrix, Matrix.add_apply, ih]

variable (C D : ChainComplex FreeQ ℤ) (hD : ∀ q < 0, (D.X q).dim = 0)

/-- The product labelling of the tensor product. -/
private def tensorLabel {α β : Type*} (LC : ∀ r, Fin (C.X r).dim → Set α)
    (LD : ∀ r, Fin (D.X r).dim → Set β) (r : ℤ)
    (a : Fin ((basedComplexTensor C D hD).X r).dim) : Set (α × β) :=
  LC ((finSigmaFinEquiv.symm a).1 : ℕ) (finProdFinEquiv.symm (finSigmaFinEquiv.symm a).2).1 ×ˢ
    LD (r - ((finSigmaFinEquiv.symm a).1 : ℕ))
      (finProdFinEquiv.symm (finSigmaFinEquiv.symm a).2).2

private lemma tensorD_entry {s : ℤ} (a' : Fin (basedComplexTensorObj C D s).dim)
    (a : Fin (basedComplexTensorObj C D (s + 1)).dim)
    (hne : toMatrix (basedComplexTensorD C D s) a' a ≠ 0) :
    ∃ p p' b' b, finSigmaFinEquiv.symm a' = ⟨p', b'⟩ ∧ finSigmaFinEquiv.symm a = ⟨p, b⟩ ∧
      toMatrix (basedComplexTensorBlock C D s p p') b' b ≠ 0 := by
  unfold basedComplexTensorD at hne
  rw [toMatrix_sum_apply] at hne
  obtain ⟨p, -, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  rw [toMatrix_sum_apply] at hp
  obtain ⟨p', -, hp'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp
  simp only [comp_toMatrix, Matrix.mul_apply] at hp'
  obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp'
  have hproj := right_ne_zero_of_mul hb
  obtain ⟨b', -, hb'⟩ := Finset.exists_ne_zero_of_sum_ne_zero (left_ne_zero_of_mul hb)
  have hinc := left_ne_zero_of_mul hb'
  have hblk := right_ne_zero_of_mul hb'
  refine ⟨p, p', b', b, ?_, ?_, hblk⟩
  · by_contra h
    exact hinc (by simp [blockInc, h])
  · by_contra h
    exact hproj (by simp [blockProj, h])

private theorem tensor_mono {α β : Type*} (LC : ∀ r, Fin (C.X r).dim → Set α)
    (LD : ∀ r, Fin (D.X r).dim → Set β) (hC : LabelMono C LC) (hDm : LabelMono D LD) :
    LabelMono (basedComplexTensor C D hD) (tensorLabel C D hD LC LD) := by
  intro r s a' a hne
  by_cases hrs : s + 1 = r
  swap
  · exact absurd (by rw [(basedComplexTensor C D hD).shape r s (by simp; omega)]; rfl) hne
  subst hrs
  rw [basedComplexTensor_d] at hne
  obtain ⟨p, p', b', b, ha', ha, hblk⟩ := tensorD_entry C D a' a hne
  unfold tensorLabel
  rw [ha', ha]
  unfold basedComplexTensorBlock at hblk
  split_ifs at hblk with h1 h2
  · rw [basedKron_entry] at hblk
    have hc := hC _ _ _ _ (left_ne_zero_of_mul hblk)
    have hy := eqToHom_entry (congrArg D.X (show s + 1 - ((p : ℕ) : ℤ) = s - ((p' : ℕ) : ℤ) by omega))
      _ _ (right_ne_zero_of_mul hblk)
    rw [label_congr D LD (show s - ((p' : ℕ) : ℤ) = s + 1 - ((p : ℕ) : ℤ) by omega) _ _ hy]
    exact Set.prod_mono hc le_rfl
  · rw [smul_toMatrix, Matrix.smul_apply, basedKron_entry, smul_eq_mul] at hblk
    have hm := right_ne_zero_of_mul hblk
    have hx := eqToHom_entry (congrArg C.X (show ((p : ℕ) : ℤ) = ((p' : ℕ) : ℤ) by omega))
      _ _ (left_ne_zero_of_mul hm)
    have hd := hDm _ _ _ _ (right_ne_zero_of_mul hm)
    rw [label_congr C LC (show ((p' : ℕ) : ℤ) = ((p : ℕ) : ℤ) by omega) _ _ hx]
    exact Set.prod_mono le_rfl hd
  · exact absurd rfl hblk


omit hD in
private lemma labelMono_congr {α : Type*} {L L' : ∀ r, Fin (C.X r).dim → Set α} (h : LabelMono C L)
    (hL : ∀ r a, L' r a = L r a) : LabelMono C L' := by
  intro r s a' a hne
  rw [hL, hL]
  exact h r s a' a hne

omit hD in
private lemma labelMono_preimage {α β : Type*} {L : ∀ r, Fin (C.X r).dim → Set α} (h : LabelMono C L)
    (g : β → α) : LabelMono C (fun r a => g ⁻¹' L r a) :=
  fun r s a' a hne => Set.preimage_mono (h r s a' a hne)

private lemma circle_mono (k : ℕ) :
    LabelMono (circleComplex k) (fun r w => cellRealization k (circleCell k r w)) := by
  intro r s a' a hne
  by_cases hrs : s + 1 = r
  swap
  · exact absurd (by rw [(circleComplex k).shape r s (by simp; omega)]; rfl) hne
  subst hrs
  have hd : (circleComplex k).d (s + 1) s = circleD k s :=
    ChainComplex.of_d (fun r => (⟨circleDim k r⟩ : FreeQ)) (circleD k) s
  by_cases hs : s = 0
  swap
  · have h0 : circleD k s = 0 := by
      rcases s with (_ | m) | m
      · exact absurd rfl hs
      · rfl
      · rfl
    rw [hd, h0] at hne
    exact absurd rfl hne
  subst hs
  rw [hd] at hne
  obtain ⟨w', hw'⟩ := a'
  obtain ⟨w, hw⟩ := a
  change w' < k at hw'
  change w < k at hw
  change (circleDiffMatrix k) ⟨w', hw'⟩ ⟨w, hw⟩ ≠ 0 at hne
  change cellRealization k (⟨w', hw'⟩, false) ⊆ cellRealization k (⟨w, hw⟩, true)
  simp only [circleDiffMatrix, Matrix.of_apply, Fin.mk.injEq] at hne
  have hk : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hle : (4 * (w : ℝ) / k) ≤ 4 * ((w : ℝ) + 1) / k := by gcongr; linarith
  simp only [cellRealization, Bool.false_eq_true, ite_false, ite_true, Set.singleton_subset_iff]
  by_cases h1 : w' = (w + 1) % k
  · by_cases hlt : w + 1 < k
    · rw [Nat.mod_eq_of_lt hlt] at h1
      subst h1
      exact ⟨_, ⟨hle, le_rfl⟩, by push_cast; rfl⟩
    · have hw1 : w + 1 = k := by omega
      rw [hw1, Nat.mod_self] at h1
      subst h1
      refine ⟨4 * ((w : ℝ) + 1) / k, ⟨hle, le_rfl⟩, ?_⟩
      have : ((w : ℝ) + 1) = k := by exact_mod_cast hw1
      rw [this, mul_div_assoc, div_self hk.ne', mul_one]
      simp [AddCircle.coe_period]
  · have h2 : w' = w := by
      by_contra h2
      exact hne (by simp [h1, h2])
    subst h2
    exact ⟨_, ⟨le_rfl, hle⟩, rfl⟩


private lemma realization_snoc {k n : ℕ} (c : GridCube k n) (b : Fin k × Bool) :
    GridCube.realization (Fin.snoc c b : GridCube k (n + 1)) =
      (fun t : Torus (n + 1) => (Fin.init t, t (Fin.last n))) ⁻¹'
        (c.realization ×ˢ cellRealization k b) := by
  ext t
  simp only [GridCube.realization, Set.mem_preimage, Set.mem_prod, Set.mem_pi, Set.mem_univ,
    true_implies, Fin.forall_fin_succ', Fin.snoc_castSucc, Fin.snoc_last, Fin.init]

private lemma unit_mono {α : Type*} (L : ∀ r, Fin (unitComplex.X r).dim → Set α) :
    LabelMono unitComplex L := by
  intro r s a' a hne
  exfalso
  by_cases hrs : s + 1 = r
  · subst hrs
    have h0 : unitComplex.d (s + 1) s = 0 :=
      ChainComplex.of_d (fun r => (⟨unitDim r⟩ : FreeQ)) (fun _ => 0) s
    rw [h0] at hne
    exact hne rfl
  · exact hne (by rw [unitComplex.shape r s (by simp; omega)]; rfl)

private lemma grid_mono (k : ℕ) :
    ∀ n, LabelMono (gridComplex k n) (fun r a => (gridCell k n r a).realization)
  | 0 => unit_mono _
  | n + 1 =>
    labelMono_congr _
      (labelMono_preimage _
        (tensor_mono (gridComplex k n) (circleComplex k) (circleComplex_dim_neg k) _ _
          (grid_mono k n) (circle_mono k))
        (fun t : Torus (n + 1) => (Fin.init t, t (Fin.last n))))
      (fun _ _ => realization_snoc _ _)


end Face

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The face lemma for the chain model. -/
private theorem chainModel_face (A : LocalDatum p n D ρplus) (i : ℕ) (r s : ℤ)
    (a' : Fin ((chainModel A i).X s).dim) (a : Fin ((chainModel A i).X r).dim)
    (hne : toMatrix ((chainModel A i).d r s) a' a ≠ 0) :
    (chainModelCube A i s a').realization ⊆ (chainModelCube A i r a).realization := by
  have h := tensor_mono (gridComplex (meshSequence A i) n) cp2Complex cp2Complex_dim_neg
    (fun r a => (gridCell (meshSequence A i) n r a).realization)
    (fun _ _ => (Set.univ : Set Unit)) (grid_mono _ n) (fun _ _ _ _ _ => le_rfl) r s a' a hne
  rcases Set.prod_subset_prod_iff.mp h with h | h | h
  · exact h.1
  · exact fun x hx => absurd (h ▸ hx : x ∈ (∅ : Set _)) (Set.notMem_empty x)
  · exact absurd h (Set.univ_nonempty.ne_empty)

private theorem retainedProj_apply (F : FixedLocalData p n D ρplus) {i : ℕ}
    (hi : startIndex F ≤ i) (s : ℤ) (b) (a) :
    retainedProj F i s b a = if a = compressedCell F hi s b then 1 else 0 := by
  simp [retainedProj, hi]

private theorem compressedCell_retained (F : FixedLocalData p n D ρplus) {i : ℕ}
    (hi : startIndex F ≤ i) (s : ℤ) (b : Fin ((compressed F s).as.n i)) :
    IsRetained F i s (compressedCell F hi s b) :=
  (mem_retainedCells F i s _).1 (Finset.orderEmbOfFin_mem _ _ b)

private theorem exists_compressedCell (F : FixedLocalData p n D ρplus) {i : ℕ}
    (hi : startIndex F ≤ i) (r : ℤ) (a) (ha : IsRetained F i r a) :
    ∃ c : Fin ((compressed F r).as.n i), compressedCell F hi r c = a := by
  have hc : (retainedCells F i r).card = compressedDim F i r := by simp [compressedDim, hi]
  have : a ∈ Set.range ((retainedCells F i r).orderEmbOfFin hc) := by
    rw [Finset.range_orderEmbOfFin]
    exact (mem_retainedCells F i r a).2 ha
  exact this

private theorem compressedCell_injective (F : FixedLocalData p n D ρplus) {i : ℕ}
    (hi : startIndex F ≤ i) (r : ℤ) :
    Function.Injective (fun b : Fin ((compressed F r).as.n i) => compressedCell F hi r b) :=
  ((retainedCells F i r).orderEmbOfFin _).injective

/-- **The discarded cells form a subcomplex.** `pr_i d Q_i = 0` and `Q_i^* d^* pr_i^* = 0`, for
the component `d : (D_i)_r → (D_i)_s` of the differential of `D_i`. -/
theorem pr_d_Q (F : FixedLocalData p n D ρplus) (i : ℕ) (r s : ℤ) :
    retainedProj F i s * toMatrix ((chainModel F.toLocalDatum i).d r s) *
        discardProj F i r = 0 ∧
      (discardProj F i r)ᵀ * (toMatrix ((chainModel F.toLocalDatum i).d r s))ᵀ *
        (retainedProj F i s)ᵀ = 0 := by
  have h1 : retainedProj F i s * toMatrix ((chainModel F.toLocalDatum i).d r s) *
      discardProj F i r = 0 := by
    classical
    by_cases hi : startIndex F ≤ i
    swap
    · ext b
      have h0 : (compressed F s).as.n i = 0 := by
        show compressedDim F i s = 0
        simp [compressedDim, hi]
      exact absurd b.isLt (by omega)
    set d := toMatrix ((chainModel F.toLocalDatum i).d r s)
    have key : ∀ b a, ¬ IsRetained F i r a → d (compressedCell F hi s b) a = 0 := by
      intro b a ha
      by_contra hne
      obtain ⟨x, hx1, hx2⟩ := compressedCell_retained F hi s b
      exact ha ⟨x, chainModel_face _ i r s _ a hne hx1, hx2⟩
    have hpd : ∀ b a, (retainedProj F i s * d) b a = d (compressedCell F hi s b) a := by
      intro b a
      simp [Matrix.mul_apply, retainedProj_apply F hi]
    have hip : ∀ a₁ a, (retainedInc F i r * retainedProj F i r) a₁ a =
        if IsRetained F i r a ∧ a₁ = a then 1 else 0 := by
      intro a₁ a
      simp only [retainedInc, Matrix.mul_apply, Matrix.transpose_apply, retainedProj_apply F hi]
      by_cases ha : IsRetained F i r a
      · obtain ⟨c, rfl⟩ := exists_compressedCell F hi r a ha
        rw [Finset.sum_eq_single c]
        · by_cases h : a₁ = compressedCell F hi r c <;> simp [h, ha]
        · intro c' _ hc'
          have : compressedCell F hi r c ≠ compressedCell F hi r c' :=
            fun e => hc' (compressedCell_injective F hi r e).symm
          simp [this]
        · simp
      · rw [Finset.sum_eq_zero]
        · simp [ha]
        · intro c _
          have : a ≠ compressedCell F hi r c := fun e => ha (e ▸ compressedCell_retained F hi r c)
          simp [this]
    ext b a
    simp only [discardProj, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_apply, Matrix.zero_apply,
      sub_eq_zero]
    rw [show (retainedProj F i s * d * (retainedInc F i r * retainedProj F i r)) b a =
        ∑ a₁, (retainedProj F i s * d) b a₁ * (retainedInc F i r * retainedProj F i r) a₁ a from
      Matrix.mul_apply]
    simp only [hpd, hip]
    by_cases ha : IsRetained F i r a
    · simp [ha]
    · simp [ha, key b a ha]
  refine ⟨h1, ?_⟩
  rw [Matrix.mul_assoc, ← Matrix.transpose_mul, ← Matrix.transpose_mul, h1, Matrix.transpose_zero]

end HSP.Compression
