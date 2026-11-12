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
  rw [this]
  refine isClosed_iUnion_of_finite fun k => ?_
  by_cases h : k.val < n - m + 1
  · simpa [h] using isClosed_eq ((continuous_coord k).abs) continuous_const
  · simp [h]

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
  cases m with
  | zero => exact isClosed_univ
  | succ m =>
    rw [cutY_succ]
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

/-- The cut flag: for `1 ≤ m ≤ n`, `A_m` and `B_m` are closed, `A_m ∪ B_m = Y_{m-1}` and
`A_m ∩ B_m = Y_m`; moreover `Y_n = {y_-, y_+}` and `y_- ≠ y_+`. -/
theorem cut_flag (n : ℕ) (hn : 1 ≤ n) (s : ℝ) (hs : 0 < s) :
    (∀ m : ℕ, 1 ≤ m → m ≤ n →
      IsClosed (cutA n s m) ∧ IsClosed (cutB n s m) ∧
        cutA n s m ∪ cutB n s m = cutY n s (m - 1) ∧
        cutA n s m ∩ cutB n s m = cutY n s m) ∧
      cutY n s n = {yMinus n s, yPlus n s} ∧ yMinus n s ≠ yPlus n s := by
  refine ⟨fun m hm hmn => ⟨isClosed_closure, isClosed_cutB m, union_eq hs hm hmn, ?_⟩,
    cutY_top hn hs, yMinus_ne_yPlus hn hs⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  cases m with
  | zero => exact inter_eq_one hs hn
  | succ m => exact inter_eq_succ hs (by omega)

end HSP.Corner
