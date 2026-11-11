import Mathlib
import HilbertSmithPaper.Compression.CompressedMaps
import HilbertSmithPaper.Compression.CompressedRep
import HilbertSmithPaper.Compression.BoundSequence
import HilbertSmithPaper.Compression.BoundSequenceNull
import HilbertSmithPaper.Compression.DiscardedSubcomplex
import HilbertSmithPaper.Categories.Asymptotic.Structure.ClassEq

/-!
# Compressed differential

For `i ≥ i₀`, `d̂ d̂ = 0` and `pr_i d = d̂ pr_i`; for every `i`, `d̂` has propagation at most `δ_i`
for the labels of the compressed complex in `T × Sⁿ`. So `(C, d̂)` is a chain complex in
`𝒜_𝟏(T × Sⁿ)`, and `C_r` is a zero object for `r ∉ [0, N]`.

## Encoding

* `d̂` is written as the compression `compress F i r s (d r s)` of the component `d r s` of the
  differential of `D_i`, for all `r s` (it is `0` unless `s = r - 1`); the two identities are
  stated for all components. The propagation bound is stated for `d̂ : C_{r+1} → C_r`, with the
  labels `(compressed F r).as.x i` of the compressed complex and the bound sequence `bound F`.
* The chain complex is asserted to exist: a complex `C` of `𝒜_𝟏(T × Sⁿ)` with `C_r = compressed F r`
  (`hX`) whose differentials are represented (`IsCompressedRep`) by `d̂`, transported along `hX`.
  It is unique, because a morphism is determined by a representative.
* `compressed_d` (the declaration of the article) is the conjunction; `N = n + 4`.

## Proof

The identities follow from `pr_d_Q` and `d ≫ d = 0`. For the propagation, the entries of `d̂` are
entries of `d` at retained cells, which are buffered at radius `u`; the compressed labels are their
control labels, so buffer condition (3) for the differential (type `0`) gives the bound, and
`δ_i ≥ 0` covers `d̂ = 0`. The chain model has no cells outside `[0, N]` (a dimension count for
`C(k_i) ⊗ P`), so neither has `C`.
-/

open CategoryTheory CategoryTheory.Limits Filter Topology

namespace HSP.Compression

open HSP.ChainModels FreeQ
open scoped Matrix NNReal

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-! ### Chain models are concentrated in `[0, N]` -/

section Concentrated

private theorem tensor_dim_zero (C E : ChainComplex FreeQ ℤ) (hE : ∀ q < 0, (E.X q).dim = 0)
    (a b : ℕ) (hC : ∀ r : ℤ, r < 0 ∨ (a : ℤ) < r → (C.X r).dim = 0)
    (hE' : ∀ r : ℤ, r < 0 ∨ (b : ℤ) < r → (E.X r).dim = 0) (r : ℤ)
    (hr : r < 0 ∨ ((a + b : ℕ) : ℤ) < r) : ((basedComplexTensor C E hE).X r).dim = 0 := by
  show ∑ q, tensorSummandDim C E r q = 0
  refine Finset.sum_eq_zero fun q _ => ?_
  have hq := q.isLt
  by_cases hqa : (a : ℤ) < ((q : ℕ) : ℤ)
  · rw [tensorSummandDim, hC _ (Or.inr hqa), zero_mul]
  · rw [tensorSummandDim, hE' _ ?_, mul_zero]
    rcases hr with hr | hr
    · left; omega
    · right; push_cast at hr; omega

private theorem unit_dim_zero (r : ℤ) (hr : r < 0 ∨ ((0 : ℕ) : ℤ) < r) :
    (unitComplex.X r).dim = 0 := by
  show unitDim r = 0
  rcases r with (_ | m) | m
  · simp at hr
  · rfl
  · rfl

private theorem circle_dim_zero (k : ℕ) (r : ℤ) (hr : r < 0 ∨ ((1 : ℕ) : ℤ) < r) :
    ((circleComplex k).X r).dim = 0 := by
  show circleDim k r = 0
  rcases r with ((_ | _ | m)) | m
  · simp at hr
  · simp at hr
  · rfl
  · rfl

private theorem cp2_dim_zero (r : ℤ) (hr : r < 0 ∨ ((4 : ℕ) : ℤ) < r) :
    (cp2Complex.X r).dim = 0 := by
  show cp2Dim r = 0
  rw [cp2Dim_eq, ite_eq_right_iff]
  intro h
  omega

private theorem grid_dim_zero (k : ℕ) :
    ∀ m : ℕ, ∀ r : ℤ, r < 0 ∨ (m : ℤ) < r → ((gridComplex k m).X r).dim = 0
  | 0 => unit_dim_zero
  | m + 1 => tensor_dim_zero (gridComplex k m) (circleComplex k) (circleComplex_dim_neg k) m 1
      (grid_dim_zero k m) (circle_dim_zero k)

private theorem chainModel_dim_zero (A : LocalDatum p n D ρplus) (i : ℕ) (r : ℤ)
    (hr : r < 0 ∨ ((n + 4 : ℕ) : ℤ) < r) : ((chainModel A i).X r).dim = 0 :=
  tensor_dim_zero _ cp2Complex cp2Complex_dim_neg n 4 (grid_dim_zero _ n) cp2_dim_zero r hr

end Concentrated

/-! ### The compressed matrices -/

private theorem eps_nonneg (F : FixedLocalData p n D ρplus) (i : ℕ) :
    0 ≤ (buffer_eventually F).choose i :=
  (buffer_eventually F).choose_spec.2.1 i

private theorem compressed_n_zero (F : FixedLocalData p n D ρplus) {i : ℕ}
    (hi : ¬ startIndex F ≤ i) (r : ℤ) : (compressed F r).as.n i = 0 := by
  show compressedDim F i r = 0
  simp [compressedDim, hi]

private theorem retainedProj_apply' (F : FixedLocalData p n D ρplus) {i : ℕ}
    (hi : startIndex F ≤ i) (s : ℤ) (b : Fin ((compressed F s).as.n i)) (a) :
    retainedProj F i s b a = if a = compressedCell F hi s b then 1 else 0 := by
  simp [retainedProj, hi]

private theorem compress_apply (F : FixedLocalData p n D ρplus) {i : ℕ}
    (hi : startIndex F ≤ i) (r s : ℤ) (w) (b' : Fin ((compressed F s).as.n i))
    (b : Fin ((compressed F r).as.n i)) :
    compress F i r s w b' b = w (compressedCell F hi s b') (compressedCell F hi r b) := by
  simp [compress, Matrix.mul_apply, retainedProj_apply' F hi, Matrix.transpose_apply]

private theorem cell_retained (F : FixedLocalData p n D ρplus) {i : ℕ}
    (hi : startIndex F ≤ i) (r : ℤ) (b : Fin ((compressed F r).as.n i)) :
    IsRetained F i r (compressedCell F hi r b) :=
  (mem_retainedCells F i r _).1 (Finset.orderEmbOfFin_mem _ _ b)

private theorem cell_buffered (F : FixedLocalData p n D ρplus) {i : ℕ}
    (hi : startIndex F ≤ i) (r : ℤ) (b : Fin ((compressed F r).as.n i)) :
    compressedCell F hi r b ∈
      bufferedCells F.toLocalDatum F.ρ (chainModelLabel F.toLocalDatum i r) F.u := by
  obtain ⟨y, hy, hxy⟩ := ((startIndex_spec F).2 i hi).1.1 r _ (cell_retained F hi r b)
  exact ⟨y, Metric.ball_subset_ball (by linarith [F.t_lt_u]) hy, hxy⟩

private theorem compressed_x (F : FixedLocalData p n D ρplus) {i : ℕ}
    (hi : startIndex F ≤ i) (r : ℤ) (b : Fin ((compressed F r).as.n i)) :
    (compressed F r).as.x i b =
      controlLabel F.toLocalDatum F.ρ_pos F.ρ_lt (chainModelLabel F.toLocalDatum i r) F.u
        ⟨_, cell_buffered F hi r b⟩ := by
  show dite (startIndex F ≤ i) _ _ = _
  split_ifs
  rfl

private theorem prop_compress_adj (F : FixedLocalData p n D ρplus) {i : ℕ}
    (hi : startIndex F ≤ i) (r s : ℤ) (hs : s = r - 1) :
    prop ((compressed F r).as.x i) ((compressed F s).as.x i)
        (compress F i r s (toMatrix ((chainModel F.toLocalDatum i).d r s))) ≤
      ⟨_, eps_nonneg F i⟩ := by
  subst hs
  have hw : TypedMatrix.of (chainModelLabel F.toLocalDatum i r)
      (chainModelLabel F.toLocalDatum i (r - 1))
      (toMatrix ((chainModel F.toLocalDatum i).d r (r - 1))) (0 : ZMod p) ∈
        chainModelFamily F.toLocalDatum F.ρ_pos F.ρ_lt i := by
    simp only [chainModelFamily, Set.mem_union, Set.mem_ofPred_eq]
    repeat left
    exact ⟨r, rfl⟩
  have hg := ((startIndex_spec F).2 i hi).2.2 _ hw
  refine Finset.sup_le fun q hq => ?_
  have hne := (Finset.mem_filter.1 hq).2
  rw [compress_apply F hi] at hne
  have h := hg ⟨_, cell_buffered F hi (r - 1) q.1⟩ ⟨_, cell_buffered F hi r q.2⟩ hne
  simp only [TypedMatrix.of, zero_vadd] at h
  rw [compressed_x F hi r q.2, compressed_x F hi (r - 1) q.1]
  exact NNReal.coe_le_coe.1 (by rw [coe_nndist]; exact h)

private theorem prop_compress (F : FixedLocalData p n D ρplus) (i : ℕ) (r s : ℤ) :
    (prop ((compressed F r).as.x i) ((compressed F s).as.x i)
        (compress F i r s (toMatrix ((chainModel F.toLocalDatum i).d r s))) : ℝ) ≤ bound F i := by
  by_cases hi : startIndex F ≤ i
  · have hb : bound F i = (buffer_eventually F).choose i := by simp [bound, hi]
    rw [hb]
    by_cases hs : s = r - 1
    · exact NNReal.coe_le_coe.2 (prop_compress_adj F hi r s hs)
    · have h0 : (chainModel F.toLocalDatum i).d r s = 0 :=
        (chainModel F.toLocalDatum i).shape r s (by simp; omega)
      rw [h0, show toMatrix (0 : (chainModel F.toLocalDatum i).X r ⟶ _) = 0 from rfl]
      simpa [compress] using eps_nonneg F i
  · have hb : bound F i = 0 := by simp [bound, hi]
    have h0 : compress F i r s (toMatrix ((chainModel F.toLocalDatum i).d r s)) = 0 := by
      ext b
      exact (Fin.cast (compressed_n_zero F hi s) b).elim0
    rw [hb, h0, prop_zero]
    simp

private theorem compress_ident (F : FixedLocalData p n D ρplus) (i : ℕ) (r s t : ℤ) :
    compress F i s t (toMatrix ((chainModel F.toLocalDatum i).d s t)) *
        compress F i r s (toMatrix ((chainModel F.toLocalDatum i).d r s)) = 0 ∧
      retainedProj F i s * toMatrix ((chainModel F.toLocalDatum i).d r s) =
        compress F i r s (toMatrix ((chainModel F.toLocalDatum i).d r s)) *
          retainedProj F i r := by
  have hQ1 := (pr_d_Q F i s t).1
  have hQ2 := (pr_d_Q F i r s).1
  have hdd : toMatrix ((chainModel F.toLocalDatum i).d s t) *
      toMatrix ((chainModel F.toLocalDatum i).d r s) = 0 := by
    rw [← comp_toMatrix, HomologicalComplex.d_comp_d]
  simp only [discardProj, Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at hQ1 hQ2
  constructor
  · simp only [compress]
    calc _ = retainedProj F i t * toMatrix ((chainModel F.toLocalDatum i).d s t) *
          (retainedInc F i s * retainedProj F i s) *
          toMatrix ((chainModel F.toLocalDatum i).d r s) * retainedInc F i r := by
          simp only [Matrix.mul_assoc]
      _ = retainedProj F i t * (toMatrix ((chainModel F.toLocalDatum i).d s t) *
          toMatrix ((chainModel F.toLocalDatum i).d r s)) * retainedInc F i r := by
          rw [← hQ1]
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hdd]; simp
  · conv_lhs => rw [hQ2]
    simp only [compress, Matrix.mul_assoc]

/-! ### The compressed complex -/

/-- A rational matrix as an equivariant matrix for the trivial group. -/
private def um {m k : ℕ} (u : Matrix (Fin m) (Fin k) ℚ) :
    Matrix (Unit × Fin m) (Unit × Fin k) ℚ :=
  fun a b => u a.2 b.2

private theorem um_mul {l m k : ℕ} (u : Matrix (Fin l) (Fin m) ℚ) (v : Matrix (Fin m) (Fin k) ℚ) :
    um u * um v = um (u * v) := by
  ext a b
  simp [um, Matrix.mul_apply, Fintype.sum_prod_type]

private theorem prop_um {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]
    {M N : AsymPre (GroupSeq.trivial p) X} (i : ℕ)
    (u : Matrix (Fin (N.n i)) (Fin (M.n i)) ℚ) :
    prop (M.label i) (N.label i) (um u) ≤ prop (M.x i) (N.x i) u := by
  refine Finset.sup_le fun q hq => ?_
  have hne := (Finset.mem_filter.1 hq).2
  have hl : ∀ (P : AsymPre (GroupSeq.trivial p) X) (b : (GroupSeq.trivial p).G i × Fin (P.n i)),
      P.label i b = P.x i b.2 := fun P b => by
    show (GroupSeq.trivial p).χ i b.1 +ᵥ P.x i b.2 = _
    rw [show (GroupSeq.trivial p).χ i b.1 = 0 from rfl, zero_vadd]
  rw [hl, hl]
  exact Finset.le_sup (f := fun q : Fin (N.n i) × Fin (M.n i) => nndist (N.x i q.1) (M.x i q.2))
    (Finset.mem_filter.2 ⟨Finset.mem_univ (q.1.2, q.2.2), hne⟩)

/-- `d̂_i` as an equivariant matrix for the trivial group. -/
private noncomputable def dLevel (F : FixedLocalData p n D ρplus) (r s : ℤ) (i : ℕ) :
    (compressed F r).as.free i ⟶ (compressed F s).as.free i :=
  FreeCat.ofMat (um (compress F i r s (toMatrix ((chainModel F.toLocalDatum i).d r s))))
    (fun _ _ _ _ _ => rfl)

private theorem dLevel_tendsto (F : FixedLocalData p n D ρplus) (r s : ℤ) :
    Tendsto (fun i => prop ((compressed F r).as.label i) ((compressed F s).as.label i)
      (FreeCat.mat (dLevel F r s i))) atTop (𝓝 0) := by
  have h : ∀ i, (prop ((compressed F r).as.label i) ((compressed F s).as.label i)
      (FreeCat.mat (dLevel F r s i)) : ℝ) ≤ bound F i := fun i =>
    (NNReal.coe_le_coe.2 (prop_um (M := (compressed F r).as) (N := (compressed F s).as) i
      (compress F i r s (toMatrix ((chainModel F.toLocalDatum i).d r s))))).trans
      (prop_compress F i r s)
  rw [← NNReal.tendsto_coe, NNReal.coe_zero]
  exact squeeze_zero (fun _ => NNReal.coe_nonneg _) h (bound_tendsto F)

/-- The sequence `(d̂_i)` as a morphism of sequences. -/
private noncomputable def dPre (F : FixedLocalData p n D ρplus) (r s : ℤ) :
    (compressed F r).as ⟶ (compressed F s).as :=
  AsymPre.homMk (dLevel F r s) (dLevel_tendsto F r s)

private theorem mat_dPre (F : FixedLocalData p n D ρplus) (r s : ℤ) (i : ℕ) :
    FreeCat.mat (AsymPre.coord (dPre F r s) i) =
      um (compress F i r s (toMatrix ((chainModel F.toLocalDatum i).d r s))) := rfl

/-- The compressed complex `(C, d̂)`. -/
private noncomputable def compressedCx (F : FixedLocalData p n D ρplus) :
    ChainComplex (AsymCat (GroupSeq.trivial p) (F.T × Corner.RoundSphere n)) ℤ where
  X r := compressed F r
  d r s := AsymCat.mkHom (dPre F r s)
  shape r s h := by
    have : dPre F r s = 0 := AsymPre.hom_ext fun i => FreeCat.hom_ext (by
      rw [mat_dPre, (chainModel F.toLocalDatum i).shape r s h]
      ext a b
      simp [um, compress]
      rfl)
    rw [this]
    exact Functor.map_zero _ _ _
  d_comp_d' r s t _ _ := by
    refine ((Quotient.functor (asymRel (GroupSeq.trivial p) (F.T × Corner.RoundSphere n))).map_comp _ _).symm.trans ?_
    refine Eq.trans ?_ ((Quotient.functor (asymRel (GroupSeq.trivial p) (F.T × Corner.RoundSphere n))).map_zero (compressed F r).as
      (compressed F t).as)
    refine (AsymCat.mkHom_eq_iff _ _).2 ?_
    filter_upwards [eventually_ge_atTop (startIndex F)] with i hi
    refine FreeCat.hom_ext ?_
    show um (compress F i s t (toMatrix ((chainModel F.toLocalDatum i).d s t))) *
      um (compress F i r s (toMatrix ((chainModel F.toLocalDatum i).d r s))) = 0
    rw [um_mul, (compress_ident F i r s t).1]
    ext a b
    rfl

/-- **Compressed differential.** For `i ≥ i₀`, `d̂ d̂ = 0` and `pr_i d = d̂ pr_i`; for every `i`,
`d̂` has propagation at most `δ_i`; so `(C, d̂)` is a chain complex in `𝒜_𝟏(T × Sⁿ)`, and `C_r` is a
zero object for `r ∉ [0, N]`. -/
theorem compressed_d (F : FixedLocalData p n D ρplus) :
    (∀ i, startIndex F ≤ i → ∀ r s t : ℤ,
      compress F i s t (toMatrix ((chainModel F.toLocalDatum i).d s t)) *
          compress F i r s (toMatrix ((chainModel F.toLocalDatum i).d r s)) = 0 ∧
        retainedProj F i s * toMatrix ((chainModel F.toLocalDatum i).d r s) =
          compress F i r s (toMatrix ((chainModel F.toLocalDatum i).d r s)) *
            retainedProj F i r) ∧
    (∀ (i : ℕ) (r : ℤ),
      (prop ((compressed F (r + 1)).as.x i) ((compressed F r).as.x i)
        (compress F i (r + 1) r (toMatrix ((chainModel F.toLocalDatum i).d (r + 1) r))) : ℝ) ≤
          bound F i) ∧
    ∃ (C : ChainComplex (AsymCat (GroupSeq.trivial p) (F.T × Corner.RoundSphere n)) ℤ)
      (hX : ∀ r, C.X r = compressed F r),
      (∀ r s, IsCompressedRep F (eqToHom (hX r).symm ≫ C.d r s ≫ eqToHom (hX s))
        (fun i => compress F i r s (toMatrix ((chainModel F.toLocalDatum i).d r s)))) ∧
      ∀ r : ℤ, r < 0 ∨ ((n + 4 : ℕ) : ℤ) < r → IsZero (C.X r) := by
  refine ⟨fun i _ r s t => compress_ident F i r s t, fun i r => prop_compress F i (r + 1) r,
    compressedCx F, fun _ => rfl, fun r s => ⟨dPre F r s, fun i => rfl, ?_⟩, fun r hr => ?_⟩
  · show 𝟙 _ ≫ AsymCat.mkHom (dPre F r s) ≫ 𝟙 _ = _
    rw [Category.id_comp, Category.comp_id]
  · have hn : ∀ i, (compressed F r).as.n i = 0 := fun i => by
      show compressedDim F i r = 0
      unfold compressedDim
      split_ifs
      · refine Finset.card_eq_zero.2 (Finset.eq_empty_of_forall_notMem fun a _ => ?_)
        exact (Fin.cast (chainModel_dim_zero F.toLocalDatum i r hr) a).elim0
      · rfl
    have h : 𝟙 (compressed F r).as = (0 : (compressed F r).as ⟶ (compressed F r).as) :=
      AsymPre.hom_ext fun i => FreeCat.hom_ext <|
        funext fun a => absurd a.2.isLt (by simp [AsymPre.free, hn i])
    rw [IsZero.iff_id_eq_zero]
    have h2 : AsymCat.mkHom (𝟙 (compressed F r).as) = AsymCat.mkHom 0 := by rw [h]
    exact ((Quotient.functor (asymRel (GroupSeq.trivial p) (F.T × Corner.RoundSphere n))).map_id
      _).symm.trans (h2.trans (Functor.map_zero _ _ _))

end HSP.Compression
