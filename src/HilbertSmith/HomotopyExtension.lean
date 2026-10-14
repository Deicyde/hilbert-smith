import Mathlib

namespace HilbertSmith

open Set

/-- The unit interval. -/
abbrev Interval : Type := ↥(Set.Icc (0:ℝ) 1)

/-- The left endpoint of the interval. -/
def time0 : Interval := ⟨0, Set.left_mem_Icc.mpr zero_le_one⟩

/-- The `d`-sphere as unit vectors in `ℝ^{d+1}`. -/
abbrev Sphere (d : ℕ) : Type :=
  {x : EuclideanSpace ℝ (Fin (d+1)) // ‖x‖ = 1}

/-- The closed subset of the cylinder where the homotopy and the base
map paste: the full cylinder over `F0` plus the base slice. -/
def pasteSet {Y0 : Type*} [TopologicalSpace Y0] (F0 : Set Y0) :
    Set (Y0 × Interval) :=
  F0 ×ˢ Set.univ ∪ Set.univ ×ˢ {time0}

/-- The pasted map on the closed union, valued in the ambient space,
with unit norm and the two agreement properties. -/
theorem pastedMap {Y0 : Type*} [TopologicalSpace Y0] {F0 : Set Y0}
    (hF0 : IsClosed F0) {d : ℕ} (f : C(Y0, Sphere d))
    (H : C(↥F0 × Interval, Sphere d))
    (hH0 : ∀ a : ↥F0, H (a, time0) = f a) :
    ∃ PC : C(↥(pasteSet F0), EuclideanSpace ℝ (Fin (d+1))),
      (∀ z, ‖PC z‖ = 1) ∧
      (∀ (a : ↥F0) (t : Interval),
        PC ⟨(↑a, t), Or.inl ⟨a.2, trivial⟩⟩ = (H (a, t)).val) ∧
      (∀ y : Y0, PC ⟨(y, time0), Or.inr ⟨trivial, Set.mem_singleton time0⟩⟩ =
        (f y).val) := by
  classical
  set P : Y0 × Interval → EuclideanSpace ℝ (Fin (d+1)) :=
    fun z => if hz : z.1 ∈ F0 then (H (⟨z.1, hz⟩, z.2)).val
      else (f z.1).val with hP
  have hAclosed : IsClosed (F0 ×ˢ Set.univ : Set (Y0 × Interval)) :=
    hF0.prod isClosed_univ
  have hBclosed : IsClosed (Set.univ ×ˢ {time0} : Set (Y0 × Interval)) :=
    isClosed_univ.prod isClosed_singleton
  have hPA : ContinuousOn P (F0 ×ˢ Set.univ) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hEq : (F0 ×ˢ Set.univ).domRestrict P =
        fun z : ↥(F0 ×ˢ Set.univ) =>
          ((H (⟨z.1.1, (Set.mem_prod.mp z.2).1⟩, z.1.2)).val) := by
      funext z
      show P ↑z = _
      rw [hP]
      show (if hz : ((↑z : Y0 × Interval)).1 ∈ F0 then _ else _) = _
      exact dite_eq_left _
    rw [hEq]
    exact continuous_subtype_val.comp
      (H.comp ⟨fun z : ↥(F0 ×ˢ Set.univ) =>
        (⟨z.1.1, (Set.mem_prod.mp z.2).1⟩, z.1.2),
        Continuous.prodMk
          (Continuous.subtype_mk continuous_subtype_val.fst _)
          continuous_subtype_val.snd⟩).continuous
  have hPB : ContinuousOn P (Set.univ ×ˢ {time0}) := by
    have hCont : Continuous fun z : Y0 × Interval => (f z.1).val :=
      continuous_subtype_val.comp (f.continuous.comp continuous_fst)
    refine ContinuousOn.congr hCont.continuousOn (fun z hz => ?_)
    have hz2 : z.2 ∈ ({time0} : Set Interval) := (Set.mem_prod.mp hz).2
    have heq : z.2 = time0 := Set.mem_singleton_iff.mp hz2
    by_cases hzz : z.1 ∈ F0
    · rw [hP]
      show (if hz : z.1 ∈ F0 then _ else _) = (f z.1).val
      rw [dite_eq_left hzz, heq]
      have h := congrArg (fun s : Sphere d => (s.val :
        EuclideanSpace ℝ (Fin (d+1)))) (hH0 ⟨z.1, hzz⟩)
      exact h
    · rw [hP]
      show (if hz : z.1 ∈ F0 then _ else _) = (f z.1).val
      rw [dite_eq_right hzz]
  have hPC : ContinuousOn P (pasteSet F0) := by
    show ContinuousOn P (F0 ×ˢ Set.univ ∪ Set.univ ×ˢ {time0})
    exact ContinuousOn.union_of_isClosed hPA hPB hAclosed hBclosed
  refine ⟨⟨fun z => P ↑z, hPC.domRestrict⟩, ?_, ?_, ?_⟩
  · intro z
    show ‖P ↑z‖ = 1
    by_cases hzz : ((↑z : Y0 × Interval)).1 ∈ F0
    · rw [hP]
      show ‖(if hz : ((↑z : Y0 × Interval)).1 ∈ F0 then _ else _)‖ = 1
      rw [dite_eq_left hzz]
      exact (H _).prop
    · rw [hP]
      show ‖(if hz : ((↑z : Y0 × Interval)).1 ∈ F0 then _ else _)‖ = 1
      rw [dite_eq_right hzz]
      exact (f _).prop
  · intro a t
    show P _ = (H (a, t)).val
    rw [hP]
    show (if hz : (↑a, t).1 ∈ F0 then _ else _) = _
    rw [dite_eq_left a.2]
  · intro y
    show P _ = (f y).val
    by_cases hy : y ∈ F0
    · rw [hP]
      show (if hz : (y, time0).1 ∈ F0 then _ else _) = _
      rw [dite_eq_left hy]
      have h := congrArg (fun s : Sphere d => (s.val :
        EuclideanSpace ℝ (Fin (d+1)))) (hH0 ⟨y, hy⟩)
      exact h
    · rw [hP]
      show (if hz : (y, time0).1 ∈ F0 then _ else _) = _
      rw [dite_eq_right hy]

/-- Extend the pasted map coordinatewise by Tietze, agreeing on the
closed set. -/
theorem tietzeBundle {Y0 : Type*} [TopologicalSpace Y0] [CompactSpace Y0]
    [TopologicalSpace.MetrizableSpace Y0] {F0 : Set Y0} (hF0 : IsClosed F0)
    {d : ℕ}
    (PC : C(↥(pasteSet F0), EuclideanSpace ℝ (Fin (d+1)))) :
    ∃ G : C(Y0 × Interval, EuclideanSpace ℝ (Fin (d+1))),
      ∀ z : ↥(pasteSet F0), G ↑z = PC z := by
  have hC : IsClosed (pasteSet F0) := by
    show IsClosed (F0 ×ˢ Set.univ ∪ Set.univ ×ˢ {time0})
    exact (hF0.prod isClosed_univ).union
      (isClosed_univ.prod isClosed_singleton)
  choose G hG using fun j : Fin (d+1) =>
    ContinuousMap.exists_restrict_eq hC
      ⟨fun z : ↥(pasteSet F0) => PC z j, by fun_prop⟩
  have hpt : ∀ (j : Fin (d+1)) (z : ↥(pasteSet F0)), G j ↑z = PC z j :=
    fun j z => ContinuousMap.congr_fun (hG j) z
  refine ⟨⟨fun w => WithLp.toLp 2 (fun j => G j w), by fun_prop⟩, ?_⟩
  intro z
  rw [WithLp.ext_iff]
  funext j
  exact hpt j z

/-- A homotopy on a closed subset of a compact metrizable space,
starting at a given map, extends to the whole space. -/
theorem homotopyExtension {Y0 : Type*} [TopologicalSpace Y0] [CompactSpace Y0]
    [TopologicalSpace.MetrizableSpace Y0] {F0 : Set Y0} (hF0 : IsClosed F0)
    {d : ℕ} (f : C(Y0, Sphere d)) (H : C(↥F0 × Interval, Sphere d))
    (hH0 : ∀ a : ↥F0, H (a, time0) = f a) :
    ∃ Ht : C(Y0 × Interval, Sphere d),
      (∀ y : Y0, Ht (y, time0) = f y) ∧
      (∀ z : ↥F0 × Interval, Ht (↑z.1, z.2) = H z) := by
  classical
  obtain ⟨PC, hPCnorm, hPCA, hPCB⟩ := pastedMap hF0 f H hH0
  obtain ⟨G, hG⟩ := tietzeBundle hF0 PC
  have htime0_val : time0.val = 0 := rfl
  -- The good open set where the extension is large.
  set N : Set (Y0 × Interval) := {z | (1/2 : ℝ) < ‖G z‖} with hN
  have hNopen : IsOpen N := by
    rw [hN]
    exact isOpen_lt continuous_const G.continuous.norm
  have hCN : pasteSet F0 ⊆ N := by
    intro z hz
    have h1 : G z = PC ⟨z, hz⟩ := hG ⟨z, hz⟩
    have h2 : ‖PC ⟨z, hz⟩‖ = 1 := hPCnorm ⟨z, hz⟩
    show (1/2 : ℝ) < ‖G z‖
    rw [h1, h2]
    norm_num
  -- The bad projection and the good neighborhood.
  set K : Set (Y0 × Interval) := Nᶜ with hK
  have hKclosed : IsClosed K := hNopen.isClosed_compl
  have hproj : IsClosed (Prod.fst '' K) :=
    isClosedMap_fst_of_compactSpace _ hKclosed
  set U : Set Y0 := (Prod.fst '' K)ᶜ with hU
  have hF0U : F0 ⊆ U := by
    intro y hy
    show y ∈ (Prod.fst '' K)ᶜ
    rw [Set.mem_compl_iff]
    rintro ⟨z, hzK, hzy⟩
    have hmem : (y, z.2) ∈ pasteSet F0 := Or.inl ⟨hy, trivial⟩
    have hzz : z = (y, z.2) := Prod.ext hzy rfl
    have hzN : z ∈ N := by
      rw [hzz]
      exact hCN hmem
    exact hzK hzN
  have hUN : U ×ˢ Set.univ ⊆ N := by
    intro w hw
    obtain ⟨hwU, -⟩ := Set.mem_prod.mp hw
    by_contra hwN
    have hwK : w ∈ K := by
      simp only [hK, Set.mem_compl_iff]
      exact hwN
    have hcon : w.1 ∈ Prod.fst '' K := ⟨w, hwK, rfl⟩
    exact hwU hcon
  -- The cutoff function.
  have hdisj : Disjoint (Prod.fst '' K) F0 := by
    rw [Set.disjoint_left]
    intro y hcon hyF0
    exact (hF0U hyF0) hcon
  obtain ⟨μ, hμ0, hμ1, hμ01⟩ := exists_continuous_zero_one_of_isClosed
    hproj hF0 hdisj
  -- The damped time map into the cylinder.
  have hmem : ∀ z : Y0 × Interval, z.2.val * μ z.1 ∈ Set.Icc (0:ℝ) 1 := by
    intro z
    refine ⟨?_, ?_⟩
    · exact mul_nonneg z.2.2.1 (hμ01 _).1
    · have hμ := hμ01 ((↑z : Y0 × Interval)).1
      have h := mul_le_mul z.2.2.2 hμ.2 hμ.1 zero_le_one
      simpa using h
  set St : Y0 × Interval → Y0 × Interval :=
    fun z => (z.1, ⟨z.2.val * μ z.1, hmem z⟩) with hSt
  have hStcont : Continuous St := by
    rw [hSt]
    refine continuous_fst.prodMk (Continuous.subtype_mk ?_ _)
    exact (continuous_subtype_val.comp continuous_snd).mul
      (μ.continuous.comp continuous_fst)
  have hSt_fst : ∀ z : Y0 × Interval, (St z).1 = z.1 := fun z => rfl
  have hSt_snd_val : ∀ z : Y0 × Interval, (St z).2.val = z.2.val * μ z.1 :=
    fun z => rfl
  have hStN : ∀ z : Y0 × Interval, St z ∈ N := by
    intro z
    by_cases hyU : z.1 ∈ U
    · have h1 : St z ∈ U ×ˢ Set.univ := ⟨by rw [hSt_fst]; exact hyU, trivial⟩
      exact hUN h1
    · have hyP : z.1 ∈ Prod.fst '' K := by
        by_contra hcon
        have hUmem : z.1 ∈ U := by
          simp only [hU, Set.mem_compl_iff]
          exact hcon
        exact hyU hUmem
      have hμ0z : μ z.1 = 0 := hμ0 hyP
      have hs0 : (St z).2 = time0 := by
        apply Subtype.ext
        show (St z).2.val = time0.val
        rw [hSt_snd_val, hμ0z, mul_zero, htime0_val]
      have hB : St z ∈ (Set.univ ×ˢ {time0} : Set (Y0 × Interval)) := by
        refine ⟨trivial, ?_⟩
        rw [Set.mem_singleton_iff]
        exact hs0
      show St z ∈ N
      exact hCN (Or.inr hB)
  -- Normalization on nonzero vectors.
  have hnorm : ∀ v : {v : EuclideanSpace ℝ (Fin (d+1)) // ‖v‖ ≠ 0},
      ‖(‖v.1‖⁻¹ : ℝ) • v.1‖ = 1 := by
    intro v
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ v.2]
  have hpos : ∀ z : Y0 × Interval, ‖G (St z)‖ ≠ 0 := by
    intro z
    have h := hStN z
    simp only [hN, Set.mem_ofPred_eq] at h
    exact ne_of_gt (lt_trans (by norm_num) h)
  set J : C(Y0 × Interval,
      {v : EuclideanSpace ℝ (Fin (d+1)) // ‖v‖ ≠ 0}) :=
    ⟨fun z => ⟨G (St z), hpos z⟩,
      Continuous.subtype_mk (G.continuous.comp hStcont) _⟩ with hJ
  set Nm : C({v : EuclideanSpace ℝ (Fin (d+1)) // ‖v‖ ≠ 0}, Sphere d) :=
    ⟨fun v => ⟨(‖v.1‖⁻¹ : ℝ) • v.1, hnorm v⟩, by
      refine Continuous.subtype_mk ?_ _
      exact Continuous.smul
        ((continuous_subtype_val.norm).inv₀ (fun v => v.2))
        continuous_subtype_val⟩ with hNm
  have hnorm_id : ∀ (v : EuclideanSpace ℝ (Fin (d+1))) (hv : ‖v‖ = 1),
      ((‖v‖⁻¹ : ℝ) • v) = v := by
    intro v hv
    rw [hv, inv_one, one_smul]
  refine ⟨Nm.comp J, ?_, ?_⟩
  · -- Starts at `f`.
    intro y
    have hs0 : (St (y, time0)).2 = time0 := by
      apply Subtype.ext
      show (St (y, time0)).2.val = time0.val
      rw [hSt_snd_val]
      show time0.val * μ y = time0.val
      rw [htime0_val, zero_mul]
    have hSt_eq : St (y, time0) = (y, time0) := Prod.ext rfl hs0
    have hGv : G (St (y, time0)) = (f y).val := by
      rw [hSt_eq]
      exact (hG _).trans (hPCB y)
    have hGn : ‖G (St (y, time0))‖ = 1 := by
      rw [hGv]
      exact (f y).prop
    apply Subtype.ext
    show ((‖G (St (y, time0))‖⁻¹ : ℝ) • G (St (y, time0))) = (f y).val
    rw [hGn, inv_one, one_smul]
    exact hGv
  · -- Extends `H`.
    intro z
    have hμ1a : μ ↑z.1 = 1 := hμ1 z.1.2
    have hs2 : (St (↑z.1, z.2)).2 = z.2 := by
      apply Subtype.ext
      show (St (↑z.1, z.2)).2.val = z.2.val
      rw [hSt_snd_val]
      show z.2.val * μ ↑z.1 = z.2.val
      rw [hμ1a, mul_one]
    have hSt_eq : St (↑z.1, z.2) = (↑z.1, z.2) := Prod.ext rfl hs2
    have hGv : G (St (↑z.1, z.2)) = (H z).val := by
      rw [hSt_eq]
      exact (hG _).trans (hPCA z.1 z.2)
    have hGn : ‖G (St (↑z.1, z.2))‖ = 1 := by
      rw [hGv]
      exact (H z).prop
    apply Subtype.ext
    show ((‖G (St (↑z.1, z.2))‖⁻¹ : ℝ) • G (St (↑z.1, z.2))) = (H z).val
    rw [hGn, inv_one, one_smul]
    exact hGv

end HilbertSmith
