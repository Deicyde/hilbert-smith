import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.BasedVectorSpaces
import HilbertSmithPaper.LTheory.Localization.Products.BasedTensor

/-!
# Tensor product of based complexes

For chain complexes `C`, `D` of based vector spaces (`ChainComplex FreeQ ℤ`) with `D` in degrees
`≥ 0`, the complex `C ⊗ D` has `(C ⊗ D)_r = ℚ^{N_r}`, `N_r = ∑_{p=0}^{r} c_p d_{r-p}`: the summands
`C_p ⊠ D_{r-p}` (`0 ≤ p ≤ r`) are concatenated in increasing order of `p`, and inside a summand
`x_i ⊗ y_j` sits at the Kronecker position of the tensor product of based vector spaces. The
differential is `d ⊠ 1 + (-1)^p 1 ⊠ d` on `C_p ⊠ D_q`. When `C` is in degrees `≥ 0` too, these are
all the summands `C_p ⊠ D_q` with `p + q = r`.

## Encoding

* Degree `r` has the summands indexed by `p : Fin (r.toNat + 1)`; `tensorSummandDim C D r p` is
  `c_p d_{r-p}` and `basedComplexTensorObj C D r = ⟨∑_p c_p d_{r-p}⟩`. For `r < 0` the single
  summand `C_0 ⊠ D_r` is zero-dimensional, since `D` vanishes in negative degrees.
* `blockInc d j` and `blockProj d j` are the inclusion and projection of the `j`-th block of
  `ℚ^{∑ d}`, enumerated by `finSigmaFinEquiv` (concatenation in increasing `j`).
* On blocks the differential is `basedComplexTensorBlock`: `d_C ⊠ 1` from summand `p` to summand
  `p - 1`, and `(-1)^p 1 ⊠ d_D` from summand `p` to summand `p`, with the identity transports
  `D_{n+1-p} = D_{n-(p-1)}` and `C_p = C_p` written as `XIsoOfEq`.
* `basedComplexTensor C D hD` (the declaration of the article) is `ChainComplex.of` of these
  data; `d² = 0` is proved blockwise.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Kronecker

namespace HSP.ChainModels

open FreeQ

/-! ### Blocks of `ℚ^{∑ d}` -/

/-- The inclusion of the `j`-th block `ℚ^{d_j}` into `ℚ^{∑ d}`. -/
def blockInc {m : ℕ} (d : Fin m → ℕ) (j : Fin m) : (⟨d j⟩ : FreeQ) ⟶ ⟨∑ i, d i⟩ :=
  ofMatrix (Matrix.of fun a b => if finSigmaFinEquiv.symm a = ⟨j, b⟩ then 1 else 0)

/-- The projection of `ℚ^{∑ d}` onto its `j`-th block `ℚ^{d_j}`. -/
def blockProj {m : ℕ} (d : Fin m → ℕ) (j : Fin m) : (⟨∑ i, d i⟩ : FreeQ) ⟶ ⟨d j⟩ :=
  ofMatrix (Matrix.of fun b a => if finSigmaFinEquiv.symm a = ⟨j, b⟩ then 1 else 0)

private lemma blockInc_proj_apply {m : ℕ} (d : Fin m → ℕ) (j j' : Fin m) (b' : Fin (d j'))
    (b : Fin (d j)) :
    toMatrix (blockInc d j ≫ blockProj d j') b' b =
      if (⟨j', b'⟩ : (i : Fin m) × Fin (d i)) = ⟨j, b⟩ then 1 else 0 := by
  change ∑ a, (if finSigmaFinEquiv.symm a = ⟨j', b'⟩ then (1 : ℚ) else 0) *
    (if finSigmaFinEquiv.symm a = ⟨j, b⟩ then 1 else 0) = _
  rw [← Equiv.sum_comp finSigmaFinEquiv]
  simp only [Equiv.symm_apply_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]

@[reassoc (attr := simp)]
lemma blockInc_proj_self {m : ℕ} (d : Fin m → ℕ) (j : Fin m) :
    blockInc d j ≫ blockProj d j = 𝟙 _ := by
  refine Matrix.ext fun b' b => ?_
  change toMatrix (blockInc d j ≫ blockProj d j) b' b = _
  rw [blockInc_proj_apply]
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
  change _ = (1 : Matrix (Fin (d j)) (Fin (d j)) ℚ) b' b
  rw [Matrix.one_apply]

@[reassoc (attr := simp)]
lemma blockInc_proj_ne {m : ℕ} (d : Fin m → ℕ) {j j' : Fin m} (h : j ≠ j') :
    blockInc d j ≫ blockProj d j' = 0 := by
  refine Matrix.ext fun b' b => ?_
  change toMatrix (blockInc d j ≫ blockProj d j') b' b = _
  rw [blockInc_proj_apply]
  split_ifs with he
  · exact absurd (congrArg Sigma.fst he).symm h
  · rfl

/-! ### Kronecker products of morphisms -/

private lemma basedKron_comp' {X X' X'' Y Y' Y'' : FreeQ} (f : X ⟶ X') (f' : X' ⟶ X'')
    (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
    basedKron f g ≫ basedKron f' g' = basedKron (f ≫ f') (g ≫ g') := by
  change (toMatrix f' ⊗ₖ toMatrix g').submatrix finProdFinEquiv.symm finProdFinEquiv.symm *
      (toMatrix f ⊗ₖ toMatrix g).submatrix finProdFinEquiv.symm finProdFinEquiv.symm =
    ((toMatrix f' * toMatrix f) ⊗ₖ (toMatrix g' * toMatrix g)).submatrix
      finProdFinEquiv.symm finProdFinEquiv.symm
  rw [Matrix.submatrix_mul_equiv, Matrix.mul_kronecker_mul]

private lemma basedKron_zero_left {X X' Y Y' : FreeQ} (g : Y ⟶ Y') :
    basedKron (0 : X ⟶ X') g = 0 := by
  change ((0 : Matrix (Fin X'.dim) (Fin X.dim) ℚ) ⊗ₖ toMatrix g).submatrix _ _ = 0
  rw [Matrix.zero_kronecker, Matrix.submatrix_zero]; rfl

private lemma basedKron_zero_right {X X' Y Y' : FreeQ} (f : X ⟶ X') :
    basedKron f (0 : Y ⟶ Y') = 0 := by
  change (toMatrix f ⊗ₖ (0 : Matrix (Fin Y'.dim) (Fin Y.dim) ℚ)).submatrix _ _ = 0
  rw [Matrix.kronecker_zero, Matrix.submatrix_zero]; rfl

/-! ### The tensor complex -/

variable (C D : ChainComplex FreeQ ℤ)

/-- The dimension `c_p d_{r-p}` of the summand `C_p ⊠ D_{r-p}` of degree `r`. -/
abbrev tensorSummandDim (r : ℤ) (p : Fin (r.toNat + 1)) : ℕ :=
  (C.X (p : ℕ)).dim * (D.X (r - (p : ℕ))).dim

/-- The chain object `(C ⊗ D)_r = ℚ^{∑_{p=0}^{r} c_p d_{r-p}}`. -/
abbrev basedComplexTensorObj (r : ℤ) : FreeQ :=
  ⟨∑ p, tensorSummandDim C D r p⟩

/-- The block of the differential from the summand `p` of degree `n+1` to the summand `p'` of
degree `n`: `d_C ⊠ 1` if `p' = p - 1`, `(-1)^p 1 ⊠ d_D` if `p' = p`, and `0` otherwise. -/
noncomputable def basedComplexTensorBlock (n : ℤ) (p : Fin ((n + 1).toNat + 1))
    (p' : Fin (n.toNat + 1)) :
    (⟨tensorSummandDim C D (n + 1) p⟩ : FreeQ) ⟶ ⟨tensorSummandDim C D n p'⟩ :=
  if h : (p' : ℕ) + 1 = p then
    basedKron (C.d (p : ℕ) (p' : ℕ))
      (D.XIsoOfEq (show n + 1 - ((p : ℕ) : ℤ) = n - ((p' : ℕ) : ℤ) by omega)).hom
  else if h' : (p' : ℕ) = p then
    ((-1 : ℚ) ^ (p : ℕ)) •
      basedKron (C.XIsoOfEq (show ((p : ℕ) : ℤ) = ((p' : ℕ) : ℤ) by omega)).hom
        (D.d (n + 1 - (p : ℕ)) (n - (p' : ℕ)))
  else 0

/-- The differential `(C ⊗ D)_{n+1} → (C ⊗ D)_n`, assembled from its blocks. -/
noncomputable def basedComplexTensorD (n : ℤ) :
    basedComplexTensorObj C D (n + 1) ⟶ basedComplexTensorObj C D n :=
  ∑ p, ∑ p', blockProj (tensorSummandDim C D (n + 1)) p ≫ basedComplexTensorBlock C D n p p' ≫
    blockInc (tensorSummandDim C D n) p'

/-! ### `d² = 0` -/

section Square

variable {C D}

private lemma dite_of_pos {c : Prop} [inst : Decidable c] {α : Sort*} {t : c → α} {e : ¬c → α}
    (h : c) : dite c t e = t h := by
  cases inst with
  | isTrue _ => rfl
  | isFalse h' => exact absurd h h'

private lemma dite_of_neg {c : Prop} [inst : Decidable c] {α : Sort*} {t : c → α} {e : ¬c → α}
    (h : ¬c) : dite c t e = e h := by
  cases inst with
  | isTrue h' => exact absurd h' h
  | isFalse _ => rfl

/-- The `d_C ⊠ 1` part of a block. -/
private noncomputable def blockA (n : ℤ) (p : Fin ((n + 1).toNat + 1)) (p' : Fin (n.toNat + 1)) :
    (⟨tensorSummandDim C D (n + 1) p⟩ : FreeQ) ⟶ ⟨tensorSummandDim C D n p'⟩ :=
  if h : (p' : ℕ) + 1 = p then
    basedKron (C.d (p : ℕ) (p' : ℕ))
      (D.XIsoOfEq (show n + 1 - ((p : ℕ) : ℤ) = n - ((p' : ℕ) : ℤ) by omega)).hom
  else 0

/-- The `(-1)^p 1 ⊠ d_D` part of a block. -/
private noncomputable def blockB (n : ℤ) (p : Fin ((n + 1).toNat + 1)) (p' : Fin (n.toNat + 1)) :
    (⟨tensorSummandDim C D (n + 1) p⟩ : FreeQ) ⟶ ⟨tensorSummandDim C D n p'⟩ :=
  if h' : (p' : ℕ) = p then
    ((-1 : ℚ) ^ (p : ℕ)) •
      basedKron (C.XIsoOfEq (show ((p : ℕ) : ℤ) = ((p' : ℕ) : ℤ) by omega)).hom
        (D.d (n + 1 - (p : ℕ)) (n - (p' : ℕ)))
  else 0

private lemma block_eq (n : ℤ) (p : Fin ((n + 1).toNat + 1)) (p' : Fin (n.toNat + 1)) :
    basedComplexTensorBlock C D n p p' = blockA n p p' + blockB n p p' := by
  unfold basedComplexTensorBlock blockA blockB
  by_cases h : (p' : ℕ) + 1 = p
  · have h' : ¬ (p' : ℕ) = p := by omega
    rw [dite_of_pos h, dite_of_pos h, dite_of_neg h', add_zero]
  · rw [dite_of_neg h, dite_of_neg h, zero_add]

private lemma blockA_comp_blockA (n : ℤ) (p : Fin ((n + 1 + 1).toNat + 1))
    (p' : Fin ((n + 1).toNat + 1)) (q : Fin (n.toNat + 1)) :
    blockA (C := C) (D := D) (n + 1) p p' ≫ blockA n p' q = 0 := by
  unfold blockA
  by_cases h1 : (p' : ℕ) + 1 = p
  · by_cases h2 : (q : ℕ) + 1 = p'
    · rw [dite_of_pos h1, dite_of_pos h2, basedKron_comp', HomologicalComplex.d_comp_d,
        basedKron_zero_left]
    · rw [dite_of_neg h2, comp_zero]
  · rw [dite_of_neg h1, zero_comp]

private lemma blockB_comp_blockB (n : ℤ) (p : Fin ((n + 1 + 1).toNat + 1))
    (p' : Fin ((n + 1).toNat + 1)) (q : Fin (n.toNat + 1)) :
    blockB (C := C) (D := D) (n + 1) p p' ≫ blockB n p' q = 0 := by
  unfold blockB
  by_cases h1 : (p' : ℕ) = p
  · by_cases h2 : (q : ℕ) = p'
    · rw [dite_of_pos h1, dite_of_pos h2, Linear.smul_comp, Linear.comp_smul, basedKron_comp',
        HomologicalComplex.d_comp_d, basedKron_zero_right, smul_zero, smul_zero]
    · rw [dite_of_neg h2, comp_zero]
  · rw [dite_of_neg h1, zero_comp]

private lemma mixed_sum (hD : ∀ q < 0, (D.X q).dim = 0) (n : ℤ)
    (p : Fin ((n + 1 + 1).toNat + 1)) (q : Fin (n.toNat + 1)) :
    ∑ p', (blockA (C := C) (D := D) (n + 1) p p' ≫ blockB n p' q +
      blockB (n + 1) p p' ≫ blockA n p' q) = 0 := by
  by_cases hQ : n < ((q : ℕ) : ℤ)
  · -- the target summand is zero-dimensional
    have h0 : tensorSummandDim C D n q = 0 := by
      simp only [tensorSummandDim, hD (n - ((q : ℕ) : ℤ)) (by omega), mul_zero]
    refine Matrix.ext fun i _ => ?_
    exact (Fin.cast h0 i).elim0
  rw [not_lt] at hQ
  by_cases hPQ : (q : ℕ) + 1 = p
  · have hq1 : (q : ℕ) < (n + 1).toNat + 1 := by omega
    have hp2 : (p : ℕ) < (n + 1).toNat + 1 := by omega
    have e1 : ∑ p', blockA (C := C) (D := D) (n + 1) p p' ≫ blockB n p' q =
        blockA (n + 1) p ⟨q, hq1⟩ ≫ blockB n ⟨q, hq1⟩ q := by
      refine Finset.sum_eq_single _ (fun p' _ hp' => ?_) (fun h => absurd (Finset.mem_univ _) h)
      unfold blockB
      rw [dite_of_neg (fun h => hp' (Fin.ext h.symm)), comp_zero]
    have e2 : ∑ p', blockB (C := C) (D := D) (n + 1) p p' ≫ blockA n p' q =
        blockB (n + 1) p ⟨p, hp2⟩ ≫ blockA n ⟨p, hp2⟩ q := by
      refine Finset.sum_eq_single _ (fun p' _ hp' => ?_) (fun h => absurd (Finset.mem_univ _) h)
      unfold blockB
      rw [dite_of_neg (fun h => hp' (Fin.ext h)), zero_comp]
    rw [Finset.sum_add_distrib, e1, e2]
    unfold blockA blockB
    rw [dite_of_pos (show ((⟨q, hq1⟩ : Fin ((n + 1).toNat + 1)) : ℕ) + 1 = p from hPQ),
      dite_of_pos (show (q : ℕ) = ((⟨q, hq1⟩ : Fin ((n + 1).toNat + 1)) : ℕ) from rfl),
      dite_of_pos (show ((⟨p, hp2⟩ : Fin ((n + 1).toNat + 1)) : ℕ) = p from rfl),
      dite_of_pos (show (q : ℕ) + 1 = ((⟨p, hp2⟩ : Fin ((n + 1).toNat + 1)) : ℕ) from hPQ)]
    simp only [Linear.smul_comp, Linear.comp_smul, basedKron_comp',
      HomologicalComplex.d_comp_XIsoOfEq_hom, HomologicalComplex.XIsoOfEq_hom_comp_d]
    have hs : ((-1 : ℚ) ^ (p : ℕ)) = -((-1) ^ (q : ℕ)) := by rw [← hPQ, pow_succ]; ring
    rw [← add_smul, hs, add_neg_cancel, zero_smul]
  · refine Finset.sum_eq_zero fun p' _ => ?_
    unfold blockA blockB
    by_cases h1 : (p' : ℕ) + 1 = p
    · rw [dite_of_pos h1, dite_of_neg (show ¬ (q : ℕ) = p' by omega), comp_zero,
        dite_of_neg (show ¬ (p' : ℕ) = p by omega), zero_comp, add_zero]
    · rw [dite_of_neg h1, zero_comp, zero_add]
      by_cases h2 : (p' : ℕ) = p
      · rw [dite_of_neg (show ¬ (q : ℕ) + 1 = p' by omega), comp_zero]
      · rw [dite_of_neg h2, zero_comp]

private lemma blocks_sum (hD : ∀ q < 0, (D.X q).dim = 0) (n : ℤ)
    (p : Fin ((n + 1 + 1).toNat + 1)) (q : Fin (n.toNat + 1)) :
    ∑ p', basedComplexTensorBlock C D (n + 1) p p' ≫ basedComplexTensorBlock C D n p' q = 0 := by
  simp only [block_eq, Preadditive.add_comp, Preadditive.comp_add, blockA_comp_blockA,
    blockB_comp_blockB, zero_add, add_zero]
  rw [← mixed_sum hD n p q]
  exact Finset.sum_congr rfl fun p' _ => add_comm _ _

end Square

private lemma blockInc_comp_D (n : ℤ) (p' : Fin ((n + 1).toNat + 1)) :
    blockInc (tensorSummandDim C D (n + 1)) p' ≫ basedComplexTensorD C D n =
      ∑ q', basedComplexTensorBlock C D n p' q' ≫ blockInc (tensorSummandDim C D n) q' := by
  unfold basedComplexTensorD
  rw [Preadditive.comp_sum, Finset.sum_eq_single p']
  · rw [Preadditive.comp_sum]; simp only [blockInc_proj_self_assoc]
  · intro q _ hq
    rw [Preadditive.comp_sum]
    simp only [blockInc_proj_ne_assoc _ (Ne.symm hq), zero_comp, Finset.sum_const_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `d² = 0` for the tensor differential. -/
lemma basedComplexTensorD_comp (hD : ∀ q < 0, (D.X q).dim = 0) (n : ℤ) :
    basedComplexTensorD C D (n + 1) ≫ basedComplexTensorD C D n = 0 := by
  conv_lhs => rw [basedComplexTensorD]
  rw [Preadditive.sum_comp]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [Preadditive.sum_comp]
  simp only [Category.assoc, blockInc_comp_D, Preadditive.comp_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun q _ => ?_
  have e : ∑ p', blockProj (tensorSummandDim C D (n + 1 + 1)) p ≫
      basedComplexTensorBlock C D (n + 1) p p' ≫ basedComplexTensorBlock C D n p' q ≫
        blockInc (tensorSummandDim C D n) q =
      blockProj (tensorSummandDim C D (n + 1 + 1)) p ≫
        (∑ p', basedComplexTensorBlock C D (n + 1) p p' ≫ basedComplexTensorBlock C D n p' q) ≫
          blockInc (tensorSummandDim C D n) q := by
    rw [Preadditive.sum_comp, Preadditive.comp_sum]
    simp only [Category.assoc]
  rw [e, blocks_sum hD, zero_comp, comp_zero]

/-- **Tensor product of based complexes.** For complexes `C`, `D` of based vector spaces with `D`
in degrees `≥ 0`, `(C ⊗ D)_r = ℚ^{∑_{p=0}^{r} c_p d_{r-p}}` (summands in increasing `p`, Kronecker
positions inside), with differential `d ⊠ 1 + (-1)^p 1 ⊠ d` on `C_p ⊠ D_{r-p}`. -/
noncomputable def basedComplexTensor (hD : ∀ q < 0, (D.X q).dim = 0) : ChainComplex FreeQ ℤ :=
  ChainComplex.of (basedComplexTensorObj C D) (basedComplexTensorD C D)
    (basedComplexTensorD_comp C D hD)

end HSP.ChainModels

namespace HSP.ChainModels

open FreeQ

variable (C D : ChainComplex FreeQ ℤ)

/-- The position of the basis vector `x_i ⊗ y_j` of the summand `C_p ⊠ D_{r-p}` in
`(C ⊗ D)_r`: the summands are concatenated in increasing `p`, and inside a summand `x_i ⊗ y_j` is
at the Kronecker position `i · d_{r-p} + j` (0-based). -/
def tensorBasisIndex (r : ℤ) (p : Fin (r.toNat + 1)) (i : Fin (C.X (p : ℕ)).dim)
    (j : Fin (D.X (r - (p : ℕ))).dim) : Fin (basedComplexTensorObj C D r).dim :=
  finSigmaFinEquiv ⟨p, finProdFinEquiv (i, j)⟩

lemma basedComplexTensor_X (hD : ∀ q < 0, (D.X q).dim = 0) (r : ℤ) :
    (basedComplexTensor C D hD).X r = basedComplexTensorObj C D r := rfl

lemma basedComplexTensor_d (hD : ∀ q < 0, (D.X q).dim = 0) (n : ℤ) :
    (basedComplexTensor C D hD).d (n + 1) n = basedComplexTensorD C D n :=
  ChainComplex.of_d _ _ n

end HSP.ChainModels
