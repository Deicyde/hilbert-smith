import Mathlib
import HilbertSmithPaper.Corner.CutSets

/-!
# The cut flag

For `n ≥ 1`, `s > 0` and every `1 ≤ m ≤ n`: `A_m` and `B_m` are closed in `S^n`,
`A_m ∪ B_m = Y_{m-1}` and `A_m ∩ B_m = Y_m`; moreover `Y_n = {y_-, y_+}` and `y_- ≠ y_+`.
-/

namespace HSP.Corner

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
  rw [this]
  refine isClosed_iUnion_of_finite fun k => ?_
  by_cases h : k.val < n - m + 1
  · simpa [h] using isClosed_eq ((continuous_coord k).abs) continuous_const
  · simp [h]

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
  cases m with
  | zero => exact isClosed_univ
  | succ m =>
    rw [cutY_succ]
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


/-- The cut flag: for `1 ≤ m ≤ n`, `A_m` and `B_m` are closed, `A_m ∪ B_m = Y_{m-1}` and
`A_m ∩ B_m = Y_m`; moreover `Y_n = {y_-, y_+}` and `y_- ≠ y_+`. -/
theorem cut_flag (n : ℕ) (hn : 1 ≤ n) (s : ℝ) (hs : 0 < s) :
    (∀ m : ℕ, 1 ≤ m → m ≤ n →
      IsClosed (cutA n s m) ∧ IsClosed (cutB n s m) ∧
        cutA n s m ∪ cutB n s m = cutY n s (m - 1) ∧
        cutA n s m ∩ cutB n s m = cutY n s m) ∧
      cutY n s n = {yMinus n s, yPlus n s} ∧ yMinus n s ≠ yPlus n s := by
  refine ⟨fun m hm1 hmn => ⟨isClosed_closure, isClosed_cutB hs.le m, cutA_union hs.le hm1 hmn,
    ?_⟩, cutY_last hs hn, yMinus_ne_yPlus hs hn⟩
  rcases Nat.lt_or_ge m 2 with hm | hm
  · obtain rfl : m = 1 := by omega
    exact cutA_inter_one hs hn
  · obtain ⟨m, rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
    exact cutA_inter_succ hs hmn

end HSP.Corner
