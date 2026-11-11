import Mathlib
import HilbertSmithPaper.Corner.CutSets

/-!
# The cut flag

For `n ≥ 1`, `s > 0` and every `1 ≤ m ≤ n`: `A_m` and `B_m` are closed in `S^n`,
`A_m ∪ B_m = Y_{m-1}` and `A_m ∩ B_m = Y_m`; moreover `Y_n = {y_-, y_+}` and `y_- ≠ y_+`.

Proof outline (coordinates counted from `0`, so the free coordinates of `B_m` are `k < n - m + 1`).
* `B_m` and, for `m ≥ 1`, `Y_m` are images of compact subsets of `ℝ^n` (closed and bounded), so
  they are closed; `A_m` is a closure.
* `B_m ⊆ Y_{m-1}`, since `B_m` is the face `x_{n-m+1} = s` of `B_{m-1}`; as `Y_{m-1}` is closed,
  `A_m ⊆ Y_{m-1}`, which gives the union.
* Intersection. A point of `ℝ^n` lies in the closure in `S^n` of a set `W` iff it lies in the
  closure in `ℝ^n` of the part of `W` in `ℝ^n` (the inclusion is continuous and open).
  For `m = 1`: the complement of `B_1` lies in the closed set where some `|x_k| ≥ s`, so a point of
  `A_1 ∩ B_1` has some `|x_k| = s`; conversely such a point is a limit of points pushed out of the
  cube along `x_k`. For `m ≥ 2`, with `c = n - m + 1`: a point of `Y_{m-1} \ B_m` has `x_c < s`, so
  it lies in the closed set of points with some `|x_k| = s`, `k < c`, or with `x_c = -s`; a point
  of `B_m` has `x_c = s ≠ -s`. Conversely a point of `Y_m` is a limit of points with `x_c`
  lowered below `s`, which lie in `Y_{m-1} \ B_m`.
* `Y_n` has only `x_0` free, with `|x_0| = s`.
-/

open Set Filter Topology

namespace HSP.Corner

<<<<<<< HEAD
variable {n : ℕ} {s : ℝ}

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The cube face `B_m` as a subset of `ℝ^n`. -/
private def bSet (n : ℕ) (s : ℝ) (m : ℕ) : Set (E n) :=
  {x | ∀ k : Fin n, (k.val < n - m + 1 → |x k| ≤ s) ∧ (n - m + 1 ≤ k.val → x k = s)}

/-- The points with some free coordinate on the boundary. -/
private def fSet (n : ℕ) (s : ℝ) (m : ℕ) : Set (E n) :=
  {x | ∃ k : Fin n, k.val < n - m + 1 ∧ |x k| = s}

private theorem cutB_eq (m : ℕ) : cutB n s m = ((↑) : E n → RoundSphere n) '' bSet n s m := rfl

private theorem cutY_succ (m : ℕ) :
    cutY n s (m + 1) = ((↑) : E n → RoundSphere n) '' (bSet n s (m + 1) ∩ fSet n s (m + 1)) := by
  rw [image_inter OnePoint.coe_injective]
  rfl

private theorem continuous_coord (k : Fin n) : Continuous fun x : E n => x k :=
  PiLp.continuous_apply 2 _ k

private theorem isClosed_bSet (m : ℕ) : IsClosed (bSet n s m) := by
  have : bSet n s m = ⋂ k : Fin n,
      {x : E n | (k.val < n - m + 1 → |x k| ≤ s) ∧ (n - m + 1 ≤ k.val → x k = s)} := by
    ext x; simp [bSet]
  rw [this]
  refine isClosed_iInter fun k => ?_
  by_cases h1 : k.val < n - m + 1 <;> by_cases h2 : n - m + 1 ≤ k.val
  · omega
  · simpa [h1, h2] using isClosed_le ((continuous_coord k).abs) continuous_const
  · simpa [h1, h2] using isClosed_eq (continuous_coord k) continuous_const
  · omega

private theorem isClosed_fSet (m : ℕ) : IsClosed (fSet n s m) := by
  have : fSet n s m = ⋃ k : Fin n, {x : E n | k.val < n - m + 1 ∧ |x k| = s} := by
    ext x; simp [fSet]
=======
open Set Filter Topology

variable {n : ℕ} {s : ℝ}

/-- The cube face `B_m` as a subset of `ℝ^n`. -/
private def Bs (n : ℕ) (s : ℝ) (m : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ k : Fin n, (k.val < n - m + 1 → |x k| ≤ s) ∧ (n - m + 1 ≤ k.val → x k = s)}

/-- Some free coordinate of `B_m` has absolute value `s`. -/
private def Fs (n : ℕ) (s : ℝ) (m : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∃ k : Fin n, k.val < n - m + 1 ∧ |x k| = s}

private lemma cutB_eq (m : ℕ) :
    cutB n s m = ((↑) : EuclideanSpace ℝ (Fin n) → RoundSphere n) '' Bs n s m := rfl

private lemma cutY_succ (m : ℕ) :
    cutY n s (m + 1) =
      ((↑) : EuclideanSpace ℝ (Fin n) → RoundSphere n) '' (Bs n s (m + 1) ∩ Fs n s (m + 1)) := by
  rw [cutY, image_inter OnePoint.coe_injective]
  rfl

private lemma continuous_coord (k : Fin n) :
    Continuous fun x : EuclideanSpace ℝ (Fin n) => x k := by fun_prop

private lemma isClosed_Bs (m : ℕ) : IsClosed (Bs n s m) := by
  have : Bs n s m = ⋂ k : Fin n,
      ({x | k.val < n - m + 1 → |x k| ≤ s} ∩ {x | n - m + 1 ≤ k.val → x k = s}) := by
    ext x; simp [Bs]
  rw [this]
  refine isClosed_iInter fun k => IsClosed.inter ?_ ?_
  · by_cases h : k.val < n - m + 1
    · simpa [h] using isClosed_le ((continuous_coord k).abs) continuous_const
    · simp [h]
  · by_cases h : n - m + 1 ≤ k.val
    · simpa [h] using isClosed_eq (continuous_coord k) continuous_const
    · simp [h]

private lemma isClosed_Fs (m : ℕ) : IsClosed (Fs n s m) := by
  have : Fs n s m = ⋃ k : Fin n, {x | k.val < n - m + 1 ∧ |x k| = s} := by
    ext x; simp [Fs]
>>>>>>> work/af_c34efefcf14572297a47ac60
  rw [this]
  refine isClosed_iUnion_of_finite fun k => ?_
  by_cases h : k.val < n - m + 1
  · simpa [h] using isClosed_eq ((continuous_coord k).abs) continuous_const
  · simp [h]

<<<<<<< HEAD
private theorem abs_le_of_mem_bSet {m : ℕ} {x : E n} (hx : x ∈ bSet n s m) (k : Fin n) :
    |x k| ≤ |s| := by
  by_cases h : k.val < n - m + 1
  · exact ((hx k).1 h).trans (le_abs_self s)
  · rw [(hx k).2 (by omega)]

private theorem isBounded_bSet (m : ℕ) : Bornology.IsBounded (bSet n s m) := by
  refine (Metric.isBounded_closedBall (x := (0 : E n)) (r := √n * |s|)).subset fun x hx => ?_
  rw [mem_closedBall_zero_iff, EuclideanSpace.norm_eq]
  calc √(∑ k, ‖x k‖ ^ 2) ≤ √(∑ _k : Fin n, |s| ^ 2) := by
        refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun k _ => ?_)
        rw [Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_le_of_mem_bSet hx k) 2
    _ = √n * |s| := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (abs_nonneg _)]

private theorem isClosed_coe_image {K : Set (E n)} (hc : IsClosed K)
    (hb : Bornology.IsBounded K) : IsClosed (((↑) : E n → RoundSphere n) '' K) :=
  ((Metric.isCompact_of_isClosed_isBounded hc hb).image OnePoint.continuous_coe).isClosed

private theorem isClosed_cutB (m : ℕ) : IsClosed (cutB n s m) :=
  isClosed_coe_image (isClosed_bSet m) (isBounded_bSet m)

private theorem isClosed_cutY (m : ℕ) : IsClosed (cutY n s m) := by
=======
private lemma isCompact_cube :
    IsCompact {x : EuclideanSpace ℝ (Fin n) | ∀ k, |x k| ≤ s} := by
  have hK := (isCompact_univ_pi fun _ : Fin n => isCompact_Icc (a := -s) (b := s)).image
    (EuclideanSpace.equiv (Fin n) ℝ).symm.continuous
  refine hK.of_isClosed_subset ?_ fun x hx => ?_
  · have : {x : EuclideanSpace ℝ (Fin n) | ∀ k, |x k| ≤ s} = ⋂ k, {x | |x k| ≤ s} := by
      ext; simp
    rw [this]
    exact isClosed_iInter fun k => isClosed_le ((continuous_coord k).abs) continuous_const
  · refine ⟨EuclideanSpace.equiv (Fin n) ℝ x, fun k _ => abs_le.1 (hx k), ?_⟩
    simp

private lemma Bs_subset_cube (hs : 0 ≤ s) (m : ℕ) :
    Bs n s m ⊆ {x : EuclideanSpace ℝ (Fin n) | ∀ k, |x k| ≤ s} := fun x hx k => by
  by_cases h : k.val < n - m + 1
  · exact (hx k).1 h
  · rw [(hx k).2 (by omega), abs_of_nonneg hs]

private lemma isCompact_Bs (hs : 0 ≤ s) (m : ℕ) : IsCompact (Bs n s m) :=
  isCompact_cube.of_isClosed_subset (isClosed_Bs m) (Bs_subset_cube hs m)

private lemma isClosed_cutB (hs : 0 ≤ s) (m : ℕ) : IsClosed (cutB n s m) := by
  rw [cutB_eq]
  exact ((isCompact_Bs hs m).image OnePoint.continuous_coe).isClosed

private lemma isClosed_cutY (hs : 0 ≤ s) (m : ℕ) : IsClosed (cutY n s m) := by
>>>>>>> work/af_c34efefcf14572297a47ac60
  cases m with
  | zero => exact isClosed_univ
  | succ m =>
    rw [cutY_succ]
<<<<<<< HEAD
    exact isClosed_coe_image ((isClosed_bSet _).inter (isClosed_fSet _))
      ((isBounded_bSet _).subset inter_subset_left)

/-- A point of `ℝ^n` is in the closure of `W ⊆ S^n` iff it is in the closure of `W ∩ ℝ^n`. -/
private theorem coe_mem_closure_iff (W : Set (RoundSphere n)) (e : E n) :
    (e : RoundSphere n) ∈ closure W ↔ e ∈ closure (((↑) : E n → RoundSphere n) ⁻¹' W) := by
  constructor
  · intro h
    exact OnePoint.isOpenMap_coe.preimage_closure_subset_closure_preimage h
  · intro h
    exact closure_mono (image_preimage_subset _ _)
      (image_closure_subset_closure_image OnePoint.continuous_coe (mem_image_of_mem _ h))

private theorem bSet_succ_subset {m : ℕ} (hs : 0 < s) (hmn : m + 2 ≤ n) :
    bSet n s (m + 2) ⊆ bSet n s (m + 1) ∩ fSet n s (m + 1) := by
  intro x hx
  refine ⟨fun k => ⟨fun hk => ?_, fun hk => (hx k).2 (by omega)⟩,
    ⟨⟨n - m - 1, by omega⟩, by simp only; omega, ?_⟩⟩
  · by_cases h : k.val < n - (m + 2) + 1
    · exact (hx k).1 h
    · rw [(hx k).2 (by omega), abs_of_pos hs]
  · rw [(hx _).2 (by simp only; omega), abs_of_pos hs]

private theorem cutB_subset_cutY (hs : 0 < s) {m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    cutB n s m ⊆ cutY n s (m - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  cases m with
  | zero => exact subset_univ _
  | succ m =>
    rw [cutB_eq, show m + 1 + 1 - 1 = m + 1 from rfl, cutY_succ]
    exact image_mono (bSet_succ_subset hs hmn)

private theorem union_eq (hs : 0 < s) {m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    cutA n s m ∪ cutB n s m = cutY n s (m - 1) := by
  apply Subset.antisymm
  · exact union_subset (closure_minimal sdiff_subset (isClosed_cutY _))
      (cutB_subset_cutY hs hm hmn)
  · intro y hy
    by_cases hb : y ∈ cutB n s m
    · exact Or.inr hb
    · exact Or.inl (subset_closure ⟨hy, hb⟩)

/-- The perturbation of `e` in the coordinate `c` by `t`. -/
private theorem perturb_apply (e : E n) (c : Fin n) (t : ℝ) (k : Fin n) :
    (e + EuclideanSpace.single c t) k = if k = c then e k + t else e k := by
  rw [PiLp.add_apply, PiLp.single_apply]
  split_ifs <;> simp

private theorem dist_perturb (e : E n) (c : Fin n) (t : ℝ) :
    dist e (e + EuclideanSpace.single c t) = |t| := by
  rw [dist_eq_norm, sub_add_cancel_left, norm_neg, PiLp.norm_single, Real.norm_eq_abs]

private theorem inter_eq_one (hs : 0 < s) (hn : 1 ≤ n) :
    cutA n s 1 ∩ cutB n s 1 = cutY n s 1 := by
  have hcube : ∀ x : E n, x ∈ bSet n s 1 ↔ ∀ k : Fin n, |x k| ≤ s := fun x => by
    simp only [bSet]
    exact ⟨fun h k => (h k).1 (by have := k.isLt; omega),
      fun h k => ⟨fun _ => h k, fun hk => absurd hk (by have := k.isLt; omega)⟩⟩
  have hpre : ((↑) : E n → RoundSphere n) ⁻¹' (cutY n s 0 \ cutB n s 1) = (bSet n s 1)ᶜ := by
    ext x
    simp [cutY, cutB_eq, OnePoint.coe_injective.eq_iff]
  rw [cutY_succ]
  apply Subset.antisymm
  · rintro y ⟨hA, ⟨e, he, rfl⟩⟩
    refine mem_image_of_mem _ ⟨he, ?_⟩
    have hcl : e ∈ closure ((bSet n s 1)ᶜ) := by
      rw [← hpre, ← coe_mem_closure_iff]; exact hA
    have hG : closure ((bSet n s 1)ᶜ) ⊆ {x : E n | ∃ k : Fin n, s ≤ |x k|} := by
      refine closure_minimal (fun x hx => ?_) ?_
      · rw [mem_compl_iff, hcube] at hx
        simp only [not_forall, not_le] at hx
        obtain ⟨k, hk⟩ := hx
        exact ⟨k, hk.le⟩
      · have : {x : E n | ∃ k : Fin n, s ≤ |x k|} = ⋃ k : Fin n, {x : E n | s ≤ |x k|} := by
          ext x; simp
        rw [this]
        exact isClosed_iUnion_of_finite fun k => isClosed_le continuous_const
          (continuous_coord k).abs
    obtain ⟨k, hk⟩ := hG hcl
    exact ⟨k, by have := k.isLt; omega, le_antisymm ((hcube e).1 he k) hk⟩
  · rintro y ⟨e, ⟨he, ⟨k, -, hk⟩⟩, rfl⟩
    refine ⟨?_, mem_image_of_mem _ he⟩
    show (e : RoundSphere n) ∈ closure (cutY n s 0 \ cutB n s 1)
    rw [coe_mem_closure_iff, hpre]
    rw [Metric.mem_closure_iff]
    intro ε hε
    set σ : ℝ := e k / s with hσ
    have hσ2 : |σ| = 1 := by rw [hσ, abs_div, hk, abs_of_pos hs, div_self hs.ne']
    refine ⟨e + EuclideanSpace.single k (σ * (ε / 2)), ?_, ?_⟩
    · rw [mem_compl_iff, hcube]
      simp only [not_forall, not_le]
      refine ⟨k, ?_⟩
      rw [perturb_apply, ite_eq_left rfl]
      have hek : e k = σ * s := by rw [hσ, div_mul_cancel₀ _ hs.ne']
      rw [hek, ← mul_add, abs_mul, hσ2, one_mul, abs_of_pos (by positivity)]
      linarith
    · rw [dist_perturb, abs_mul, hσ2, one_mul, abs_of_pos (by positivity)]
      linarith

private theorem inter_eq_succ (hs : 0 < s) {m : ℕ} (hmn : m + 2 ≤ n) :
    cutA n s (m + 2) ∩ cutB n s (m + 2) = cutY n s (m + 2) := by
  set c : Fin n := ⟨n - m - 1, by omega⟩ with hc
  have hpre : ((↑) : E n → RoundSphere n) ⁻¹' (cutY n s (m + 1) \ cutB n s (m + 2)) =
      (bSet n s (m + 1) ∩ fSet n s (m + 1)) \ bSet n s (m + 2) := by
    ext x
    simp [cutY_succ, cutB_eq, OnePoint.coe_injective.mem_set_image]
  have hecs : ∀ x ∈ bSet n s (m + 2), x c = s := fun x hx => (hx c).2 (by simp only [hc]; omega)
  rw [cutY_succ]
  apply Subset.antisymm
  · rintro y ⟨hA, ⟨e, he, rfl⟩⟩
    refine mem_image_of_mem _ ⟨he, ?_⟩
    have hcl : e ∈ closure ((bSet n s (m + 1) ∩ fSet n s (m + 1)) \ bSet n s (m + 2)) := by
      rw [← hpre, ← coe_mem_closure_iff]; exact hA
    have hD : (bSet n s (m + 1) ∩ fSet n s (m + 1)) \ bSet n s (m + 2) ⊆
        fSet n s (m + 2) ∪ {x : E n | x c = -s} := by
      rintro x ⟨⟨hb1, ⟨k, hk, hks⟩⟩, hnb2⟩
      by_cases hkc : k.val < n - (m + 2) + 1
      · exact Or.inl ⟨k, hkc, hks⟩
      · have hkeq : k = c := Fin.ext (by simp only [hc]; omega)
        subst hkeq
        rcases (abs_eq hs.le).1 hks with h | h
        · refine absurd (fun k' => ⟨fun hk' => (hb1 k').1 (by omega), fun hk' => ?_⟩) hnb2
          by_cases hk'c : k'.val = n - m - 1
          · rw [show k' = c from Fin.ext hk'c, h]
          · exact (hb1 k').2 (by omega)
        · exact Or.inr h
    have hcl' := closure_minimal hD ((isClosed_fSet _).union
      (isClosed_eq (continuous_coord c) continuous_const)) hcl
    rcases hcl' with h | h
    · exact h
    · have h2 : e c = -s := h
      rw [hecs e he] at h2
      linarith
  · rintro y ⟨e, ⟨he, ⟨k, hk, hks⟩⟩, rfl⟩
    refine ⟨?_, mem_image_of_mem _ he⟩
    show (e : RoundSphere n) ∈ closure (cutY n s (m + 1) \ cutB n s (m + 2))
    rw [coe_mem_closure_iff, hpre, Metric.mem_closure_iff]
    intro ε hε
    have ht : 0 < min (ε / 2) s := lt_min (by positivity) hs
    have hkc : k ≠ c := fun h => by
      have := congrArg Fin.val h; simp only [hc] at this; omega
    refine ⟨e + EuclideanSpace.single c (-min (ε / 2) s),
      ⟨⟨fun k' => ⟨fun hk' => ?_, fun hk' => ?_⟩, ⟨k, by omega, ?_⟩⟩, fun hb => ?_⟩, ?_⟩
    · rw [perturb_apply]
      split_ifs with h
      · rw [h, hecs e he, abs_le]
        constructor <;> linarith [min_le_right (ε / 2) s]
      · by_cases hk'2 : k'.val < n - (m + 2) + 1
        · exact (he k').1 hk'2
        · exact absurd (Fin.ext (by simp only [hc]; omega)) h
    · rw [perturb_apply, ite_eq_right (fun h => by
        have := congrArg Fin.val h; simp only [hc] at this; omega)]
      exact (he k').2 (by omega)
    · rw [perturb_apply, ite_eq_right hkc]; exact hks
    · have h1 := hecs _ hb
      rw [perturb_apply, ite_eq_left rfl, hecs e he] at h1
      linarith
    · rw [dist_perturb, abs_neg, abs_of_pos ht]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)

private theorem cutY_top (hn : 1 ≤ n) (hs : 0 < s) : cutY n s n = {yMinus n s, yPlus n s} := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [cutY_succ]
  ext y
  constructor
  · rintro ⟨e, ⟨hb, ⟨k, hk, hks⟩⟩, rfl⟩
    have hk0 : k.val = 0 := by omega
    have hrest : ∀ k' : Fin (m + 1), k'.val ≠ 0 → e k' = s := fun k' hk' => (hb k').2 (by omega)
    rcases (abs_eq hs.le).1 hks with h | h
    · right
      show (e : RoundSphere (m + 1)) = ((WithLp.toLp 2 fun _ : Fin (m + 1) => s : E (m + 1)) : _)
      congr 1
      refine PiLp.ext fun k' => ?_
      by_cases hk' : k'.val = 0
      · rw [show k' = k from Fin.ext (by omega), h]
      · rw [hrest k' hk']
    · left
      show (e : RoundSphere (m + 1)) = ((WithLp.toLp 2 fun k : Fin (m + 1) =>
        if k.val = 0 then -s else s : E (m + 1)) : _)
      congr 1
      refine PiLp.ext fun k' => ?_
      by_cases hk' : k'.val = 0
      · rw [show k' = k from Fin.ext (by omega), h]
        show -s = if k.val = 0 then -s else s
        rw [ite_eq_left hk0]
      · rw [hrest k' hk']
        show s = if k'.val = 0 then -s else s
        rw [ite_eq_right hk']
  · rintro (rfl | rfl)
    · refine ⟨_, ⟨fun k => ⟨fun _ => ?_, fun hk => ?_⟩, ⟨0, by simp, ?_⟩⟩, rfl⟩
      · show |if k.val = 0 then -s else s| ≤ s
        split_ifs <;> simp [abs_of_pos hs]
      · show (if k.val = 0 then -s else s) = s
        rw [ite_eq_right (by omega)]
      · show |if (0 : Fin (m + 1)).val = 0 then -s else s| = s
        simp [abs_of_pos hs]
    · refine ⟨_, ⟨fun k => ⟨fun _ => ?_, fun _ => rfl⟩, ⟨0, by simp, ?_⟩⟩, rfl⟩
      · show |s| ≤ s
        rw [abs_of_pos hs]
      · show |s| = s
        rw [abs_of_pos hs]

private theorem yMinus_ne_yPlus (hn : 1 ≤ n) (hs : 0 < s) : yMinus n s ≠ yPlus n s := by
  intro h
  have h1 := congrArg (fun v : E n => v ⟨0, hn⟩) (OnePoint.coe_injective h)
  change (if (0 : ℕ) = 0 then -s else s) = s at h1
  rw [ite_eq_left rfl] at h1
  linarith

=======
    exact (((isCompact_Bs hs (m + 1)).inter_right (isClosed_Fs (m + 1))).image
      OnePoint.continuous_coe).isClosed

private lemma cutB_subset_cutY (hs : 0 ≤ s) {m : ℕ} (hm1 : 1 ≤ m) (hmn : m ≤ n) :
    cutB n s m ⊆ cutY n s (m - 1) := by
  rcases Nat.lt_or_ge m 2 with hm | hm
  · obtain rfl : m = 1 := by omega
    exact subset_univ _
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  rw [cutB_eq, show m + 2 - 1 = m + 1 by omega, cutY_succ]
  refine image_mono fun x hx => ⟨fun k => ⟨fun hk => ?_, fun hk => (hx k).2 (by omega)⟩, ?_⟩
  · by_cases h : k.val < n - (m + 2) + 1
    · exact (hx k).1 h
    · rw [(hx k).2 (by omega), abs_of_nonneg hs]
  · refine ⟨⟨n - (m + 2) + 1, by omega⟩, by simp only; omega, ?_⟩
    rw [(hx _).2 (by simp only; omega), abs_of_nonneg hs]

private lemma cutA_union (hs : 0 ≤ s) {m : ℕ} (hm1 : 1 ≤ m) (hmn : m ≤ n) :
    cutA n s m ∪ cutB n s m = cutY n s (m - 1) := by
  refine subset_antisymm (union_subset ?_ (cutB_subset_cutY hs hm1 hmn)) fun y hy => ?_
  · exact closure_minimal sdiff_subset (isClosed_cutY hs (m - 1))
  · by_cases hb : y ∈ cutB n s m
    · exact Or.inr hb
    · exact Or.inl (subset_closure ⟨hy, hb⟩)

/-- Moving coordinate `k` of `x` by `t c`. -/
private lemma coord_move (x : EuclideanSpace ℝ (Fin n)) (k : Fin n) (c t : ℝ) (i : Fin n) :
    (x + t • EuclideanSpace.single k c) i = if i = k then x i + t * c else x i := by
  by_cases h : i = k <;> simp [h]

private lemma tendsto_move (x : EuclideanSpace ℝ (Fin n)) (k : Fin n) (c : ℝ) :
    Tendsto (fun t : ℝ => ((x + t • EuclideanSpace.single k c : EuclideanSpace ℝ (Fin n)) :
      RoundSphere n)) (𝓝[>] 0) (𝓝 (x : RoundSphere n)) := by
  have hc : Continuous fun t : ℝ => ((x + t • EuclideanSpace.single k c :
      EuclideanSpace ℝ (Fin n)) : RoundSphere n) :=
    OnePoint.continuous_coe.comp (continuous_const.add (continuous_id.smul continuous_const))
  have := hc.tendsto 0
  simp only [zero_smul, add_zero] at this
  exact this.mono_left nhdsWithin_le_nhds

private lemma cutA_inter_one (hs : 0 < s) (hn : 1 ≤ n) :
    cutA n s 1 ∩ cutB n s 1 = cutY n s 1 := by
  rw [cutY_succ, cutA, show (1 : ℕ) - 1 = 0 from rfl, cutY, cutB_eq]
  ext y
  constructor
  · rintro ⟨hyA, ⟨x, hx, rfl⟩⟩
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    by_contra hF
    have hlt : ∀ k : Fin n, |x k| < s := fun k =>
      lt_of_le_of_ne ((hx k).1 (by omega)) fun h => hF ⟨k, by omega, h⟩
    set W : Set (EuclideanSpace ℝ (Fin n)) := {z | ∀ k, |z k| < s}
    have hW : IsOpen W := by
      have : W = ⋂ k, {z | |z k| < s} := by ext; simp [W]
      rw [this]
      exact isOpen_iInter_of_finite fun k => isOpen_lt ((continuous_coord k).abs) continuous_const
    obtain ⟨_, ⟨z, hz, rfl⟩, -, hzB⟩ := mem_closure_iff.1 hyA _
      (OnePoint.isOpenEmbedding_coe.isOpenMap W hW) ⟨x, hlt, rfl⟩
    exact hzB ⟨z, fun k => ⟨fun _ => (hz k).le, fun h => absurd k.2 (by omega)⟩, rfl⟩
  · rintro ⟨x, ⟨hx, k, hk, hxk⟩, rfl⟩
    refine ⟨?_, ⟨x, hx, rfl⟩⟩
    refine mem_closure_of_tendsto (tendsto_move x k (x k)) ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    refine ⟨trivial, ?_⟩
    rintro ⟨z, hz, hzx⟩
    have hzk := (hz k).1 (by omega)
    rw [OnePoint.coe_injective hzx, coord_move] at hzk
    simp only [↓reduceIte] at hzk
    have : |x k + t * x k| = s * (1 + t) := by
      rw [show x k + t * x k = (1 + t) * x k by ring, abs_mul, hxk,
        abs_of_pos (by linarith : (0 : ℝ) < 1 + t)]
      ring
    rw [this] at hzk
    nlinarith

private lemma cutA_inter_succ (hs : 0 < s) {m : ℕ} (hmn : m + 2 ≤ n) :
    cutA n s (m + 2) ∩ cutB n s (m + 2) = cutY n s (m + 2) := by
  have hj : n - (m + 2) + 1 < n := by omega
  set j : Fin n := ⟨n - (m + 2) + 1, hj⟩
  rw [cutA, show m + 2 - 1 = m + 1 by omega, cutY_succ, cutY_succ, cutB_eq]
  ext y
  constructor
  · rintro ⟨hyA, ⟨x, hx, rfl⟩⟩
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    by_contra hF
    have hlt : ∀ k : Fin n, k.val < n - (m + 2) + 1 → |x k| < s := fun k hk =>
      lt_of_le_of_ne ((hx k).1 hk) fun h => hF ⟨k, hk, h⟩
    set W : Set (EuclideanSpace ℝ (Fin n)) :=
      {z | (∀ k : Fin n, k.val < n - (m + 2) + 1 → |z k| < s) ∧ |z j - s| < 2 * s}
    have hW : IsOpen W := by
      have : W = (⋂ k : Fin n, {z | k.val < n - (m + 2) + 1 → |z k| < s}) ∩
          {z | |z j - s| < 2 * s} := by ext; simp [W]
      rw [this]
      refine IsOpen.inter (isOpen_iInter_of_finite fun k => ?_)
        (isOpen_lt ((continuous_coord j).sub continuous_const).abs continuous_const)
      by_cases h : k.val < n - (m + 2) + 1
      · simpa [h] using isOpen_lt ((continuous_coord k).abs) continuous_const
      · simp [h]
    have hxj : x j = s := (hx j).2 le_rfl
    obtain ⟨_, ⟨z, hz, rfl⟩, ⟨w, ⟨hwB, k, hk, hwk⟩, hwz⟩, hzB⟩ := mem_closure_iff.1 hyA _
      (OnePoint.isOpenEmbedding_coe.isOpenMap W hW) ⟨x, ⟨hlt, by rw [hxj]; simpa using hs⟩, rfl⟩
    obtain rfl := OnePoint.coe_injective hwz
    apply hzB
    refine ⟨w, fun i => ⟨fun hi => (hwB i).1 (by omega), fun hi => ?_⟩, rfl⟩
    by_cases hij : n - (m + 2) + 1 + 1 ≤ i.val
    · exact (hwB i).2 (by omega)
    obtain rfl : i = j := Fin.ext (by simp only [j]; omega)
    have hkj : k = j := by
      by_contra hne
      have : k.val < n - (m + 2) + 1 := by
        have : k.val ≠ n - (m + 2) + 1 := fun h => hne (Fin.ext h)
        omega
      exact absurd hwk (ne_of_lt (hz.1 k this))
    subst hkj
    rcases abs_eq hs.le |>.1 hwk with h | h
    · exact h
    · have := hz.2
      rw [h, show -s - s = -(2 * s) by ring, abs_neg, abs_of_pos (by linarith)] at this
      exact absurd this (lt_irrefl _)
  · rintro ⟨x, ⟨hx, k, hk, hxk⟩, rfl⟩
    refine ⟨?_, ⟨x, hx, rfl⟩⟩
    have hxj : x j = s := (hx j).2 le_rfl
    have hkj : k ≠ j := fun h => by
      have := congrArg Fin.val h; simp only [j] at this; omega
    refine mem_closure_of_tendsto (tendsto_move x j (-1)) ?_
    filter_upwards [Ioo_mem_nhdsGT (by linarith : (0 : ℝ) < 2 * s)] with t ⟨ht0, ht2⟩
    refine ⟨⟨_, ⟨fun i => ⟨fun hi => ?_, fun hi => ?_⟩, k, by omega, ?_⟩, rfl⟩, ?_⟩
    · rw [coord_move]
      split_ifs with h
      · rw [h, hxj, abs_le]; constructor <;> linarith
      · by_cases hi' : i.val < n - (m + 2) + 1
        · exact (hx i).1 hi'
        · rw [(hx i).2 (by omega), abs_of_pos hs]
    · have hij : i ≠ j := fun h => by
        have := congrArg Fin.val h; simp only [j] at this; omega
      rw [coord_move]
      simp only [hij, ↓reduceIte]
      exact (hx i).2 (by omega)
    · rw [coord_move]
      simp only [hkj, ↓reduceIte, hxk]
    · rintro ⟨z, hz, hzx⟩
      have hzj := (hz j).2 le_rfl
      rw [OnePoint.coe_injective hzx, coord_move] at hzj
      simp only [↓reduceIte, hxj] at hzj
      linarith

private lemma cutY_last (hs : 0 < s) (hn : 1 ≤ n) : cutY n s n = {yMinus n s, yPlus n s} := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [cutY_succ]
  ext y
  simp only [mem_image, mem_inter_iff, mem_insert_iff, mem_singleton_iff, yMinus, yPlus]
  constructor
  · rintro ⟨x, ⟨hx, k, hk, hxk⟩, rfl⟩
    have hk0 : k = 0 := Fin.ext (by simp only [Fin.val_zero]; omega)
    subst hk0
    have hrest : ∀ i : Fin (n' + 1), i ≠ 0 → x i = s := fun i hi =>
      (hx i).2 (by have := Fin.pos_of_ne_zero hi; omega)
    rcases abs_eq hs.le |>.1 hxk with h | h
    · right
      congr 1
      ext i
      by_cases hi : i = 0
      · subst hi; simpa using h
      · simpa using hrest i hi
    · left
      congr 1
      ext i
      by_cases hi : i = 0
      · subst hi; simpa using h
      · simp [hrest i hi, Fin.val_eq_zero_iff, hi]
  · rintro (rfl | rfl)
    · refine ⟨_, ⟨fun i => ⟨fun hi => ?_, fun hi => ?_⟩, 0, by simp, ?_⟩, rfl⟩
      · by_cases h : i.val = 0 <;> simp [h, abs_of_pos hs]
      · simp [show i.val ≠ 0 by omega]
      · simp [abs_of_pos hs]
    · refine ⟨_, ⟨fun i => ⟨fun _ => by simp [abs_of_pos hs], fun _ => by simp⟩, 0, by simp,
        by simp [abs_of_pos hs]⟩, rfl⟩

private lemma yMinus_ne_yPlus (hs : 0 < s) (hn : 1 ≤ n) : yMinus n s ≠ yPlus n s := by
  intro h
  have := congrArg (fun x : EuclideanSpace ℝ (Fin n) => x ⟨0, hn⟩) (OnePoint.coe_injective h)
  simp at this
  linarith


>>>>>>> work/af_c34efefcf14572297a47ac60
/-- The cut flag: for `1 ≤ m ≤ n`, `A_m` and `B_m` are closed, `A_m ∪ B_m = Y_{m-1}` and
`A_m ∩ B_m = Y_m`; moreover `Y_n = {y_-, y_+}` and `y_- ≠ y_+`. -/
theorem cut_flag (n : ℕ) (hn : 1 ≤ n) (s : ℝ) (hs : 0 < s) :
    (∀ m : ℕ, 1 ≤ m → m ≤ n →
      IsClosed (cutA n s m) ∧ IsClosed (cutB n s m) ∧
        cutA n s m ∪ cutB n s m = cutY n s (m - 1) ∧
        cutA n s m ∩ cutB n s m = cutY n s m) ∧
      cutY n s n = {yMinus n s, yPlus n s} ∧ yMinus n s ≠ yPlus n s := by
<<<<<<< HEAD
  refine ⟨fun m hm hmn => ⟨isClosed_closure, isClosed_cutB m, union_eq hs hm hmn, ?_⟩,
    cutY_top hn hs, yMinus_ne_yPlus hn hs⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  cases m with
  | zero => exact inter_eq_one hs hn
  | succ m => exact inter_eq_succ hs (by omega)
=======
  refine ⟨fun m hm1 hmn => ⟨isClosed_closure, isClosed_cutB hs.le m, cutA_union hs.le hm1 hmn,
    ?_⟩, cutY_last hs hn, yMinus_ne_yPlus hs hn⟩
  rcases Nat.lt_or_ge m 2 with hm | hm
  · obtain rfl : m = 1 := by omega
    exact cutA_inter_one hs hn
  · obtain ⟨m, rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
    exact cutA_inter_succ hs hmn
>>>>>>> work/af_c34efefcf14572297a47ac60

end HSP.Corner
