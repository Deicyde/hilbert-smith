import Mathlib

open Set Topology Filter OnePoint

namespace HilbertSmith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

section Collapse

variable (W : Set E)

/-- The collapse map `c : S^d → W⁺`: identity on `W`, `∞` elsewhere. -/
noncomputable def collapse : OnePoint E → OnePoint ↥W := by
  classical
  exact fun x => x.elim ∞ (fun z => if h : z ∈ W then ↑(⟨z, h⟩ : ↥W) else ∞)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
@[simp] theorem collapse_infty : collapse W ∞ = ∞ := rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
@[simp] theorem collapse_coe_mem {z : E} (h : z ∈ W) :
    collapse W ↑z = ↑(⟨z, h⟩ : ↥W) := dite_eq_left h

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
@[simp] theorem collapse_coe_notMem {z : E} (h : z ∉ W) :
    collapse W ↑z = ∞ := dite_eq_right h

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Preimage of a set missing `∞`: points of `W` over the preimage. -/
theorem collapse_preimage_of_notMem {s : Set (OnePoint ↥W)} (h : ∞ ∉ s) :
    collapse W ⁻¹' s = (↑) '' (Subtype.val '' (((↑) : ↥W → OnePoint ↥W) ⁻¹' s)) := by
  ext x
  induction x using OnePoint.rec with
  | infty =>
    simp only [Set.mem_preimage, collapse_infty, Set.mem_image]
    constructor
    · intro hmem; exact absurd hmem h
    · rintro ⟨y, -, hcon⟩
      exact (OnePoint.coe_ne_infty y hcon).elim
  | coe z =>
    by_cases hz : z ∈ W
    · simp only [collapse_coe_mem W hz, Set.mem_preimage, Set.mem_image]
      constructor
      · intro hmem
        exact ⟨z, ⟨⟨z, hz⟩, hmem, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨w, hmem, rfl⟩, hxz⟩
        have hxz' : w.val = z := OnePoint.coe_injective hxz
        subst hxz'
        have : (⟨w.val, hz⟩ : ↥W) = w := Subtype.ext rfl
        rw [this]
        exact hmem
    · simp only [Set.mem_preimage, collapse_coe_notMem W hz, Set.mem_image]
      constructor
      · intro hmem; exact absurd hmem h
      · rintro ⟨y, ⟨w, -, rfl⟩, hxz⟩
        have hxz' : w.val = z := OnePoint.coe_injective hxz
        exact (hz (hxz' ▸ w.2)).elim

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Preimage of a set containing `∞`: complement of the compact core. -/
theorem collapse_preimage_of_mem {s : Set (OnePoint ↥W)} (h : ∞ ∈ s) :
    collapse W ⁻¹' s =
      ((↑) '' (Subtype.val '' ((((↑) : ↥W → OnePoint ↥W) ⁻¹' s)ᶜ)) : Set (OnePoint E))ᶜ := by
  ext x
  induction x using OnePoint.rec with
  | infty =>
    simp only [Set.mem_preimage, collapse_infty, Set.mem_compl_iff, Set.mem_image]
    constructor
    · intro _
      rintro ⟨y, -, hcon⟩
      exact OnePoint.coe_ne_infty y hcon
    · intro _; exact h
  | coe z =>
    by_cases hz : z ∈ W
    · simp only [collapse_coe_mem W hz, Set.mem_preimage, Set.mem_compl_iff,
        Set.mem_image]
      constructor
      · intro hmem hcon
        obtain ⟨y, ⟨w, hmem', rfl⟩, hxz⟩ := hcon
        have hxz' : w.val = z := OnePoint.coe_injective hxz
        subst hxz'
        have : (⟨w.val, hz⟩ : ↥W) = w := Subtype.ext rfl
        rw [this] at hmem
        exact hmem' hmem
      · intro hcon
        by_contra hmem'
        exact hcon ⟨z, ⟨⟨z, hz⟩, hmem', rfl⟩, rfl⟩
    · simp only [Set.mem_preimage, collapse_coe_notMem W hz, Set.mem_compl_iff,
        Set.mem_image]
      constructor
      · intro _
        rintro ⟨y, ⟨w, -, rfl⟩, hxz⟩
        have hxz' : w.val = z := OnePoint.coe_injective hxz
        exact hz (hxz' ▸ w.2)
      · intro _; exact h

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The collapse map is continuous, for an arbitrary open `W`. -/
theorem continuous_collapse (hW : IsOpen W) : Continuous (collapse W) := by
  rw [continuous_def]
  intro s hs
  by_cases hmem : ∞ ∈ s
  · rw [isOpen_iff_of_mem hmem] at hs
    rw [collapse_preimage_of_mem W hmem, isOpen_compl_iff, isClosed_image_coe]
    obtain ⟨hclosed, hcompact⟩ := hs
    have hc : IsCompact (Subtype.val '' ((((↑) : ↥W → OnePoint ↥W) ⁻¹' s)ᶜ)) :=
      hcompact.image continuous_subtype_val
    exact ⟨hc.isClosed, hc⟩
  · rw [isOpen_iff_of_notMem hmem] at hs
    rw [collapse_preimage_of_notMem W hmem, isOpen_image_coe]
    rw [isOpen_induced_iff] at hs
    obtain ⟨V, hV, heq⟩ := hs
    rw [← heq]
    have himg : (Subtype.val : ↥W → E) '' ((Subtype.val : ↥W → E) ⁻¹' V) = W ∩ V := by
      ext z
      simp only [Set.mem_image, Set.mem_preimage, Set.mem_inter_iff]
      constructor
      · rintro ⟨w, hmem, rfl⟩
        exact ⟨w.2, hmem⟩
      · rintro ⟨hz, hmem⟩
        exact ⟨⟨z, hz⟩, hmem, rfl⟩
    rw [himg]
    exact IsOpen.inter hW hV

end Collapse

section SecondCountable

variable (W : Set E)

/-- Open subsets of a locally compact space are locally compact. -/
theorem locallyCompactSpace_coe (hW : IsOpen W) : LocallyCompactSpace ↥W := by
  refine ⟨fun x s hs => ?_⟩
  rw [mem_nhds_iff] at hs
  obtain ⟨U, hUs, hUopen, hxU⟩ := hs
  rw [isOpen_induced_iff] at hUopen
  obtain ⟨V, hVopen, heq⟩ := hUopen
  have hxU' : x ∈ Subtype.val ⁻¹' V := heq.symm ▸ hxU
  have hxV : x.val ∈ V := hxU'
  obtain ⟨K, hKc, hxK, hKV⟩ := exists_compact_subset (hVopen.inter hW) ⟨hxV, x.2⟩
  refine ⟨Subtype.val ⁻¹' K, ?_, ?_, ?_⟩
  · have hopen : IsOpen ((Subtype.val : ↥W → E) ⁻¹' (interior K)) :=
      continuous_subtype_val.isOpen_preimage _ isOpen_interior
    exact mem_of_superset (hopen.mem_nhds hxK) (preimage_mono interior_subset)
  · intro w hw
    apply hUs
    rw [← heq]
    exact (hKV hw).1
  · rw [IsEmbedding.subtypeVal.isCompact_iff]
    rw [Set.image_preimage_eq_inter_range, Subtype.range_val]
    have hsub : K ⊆ W := fun z hz => (hKV hz).2
    rw [Set.inter_eq_self_of_subset_left hsub]
    exact hKc

/-- Opens in the countable basis with compact closure. -/
noncomputable def compactBasis : Set (Set ↥W) :=
  {U ∈ TopologicalSpace.countableBasis ↥W | IsCompact (closure U)}

theorem countable_compactBasis : (compactBasis W).Countable :=
  Set.Countable.mono (fun _ h => h.1) (TopologicalSpace.countable_countableBasis ↥W)

theorem isBasis_compactBasis (hW : IsOpen W) :
    TopologicalSpace.IsTopologicalBasis (compactBasis W) := by
  have _lc := locallyCompactSpace_coe W hW
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  · intro U hU
    exact (TopologicalSpace.isBasis_countableBasis ↥W).isOpen hU.1
  · intro a u hau hu
    obtain ⟨K, hKc, haK, hKu⟩ := exists_compact_subset hu hau
    have hVclosure : IsCompact (closure (interior K)) :=
      hKc.of_isClosed_subset isClosed_closure (closure_minimal interior_subset hKc.isClosed)
    have hVsub : interior K ⊆ u := interior_subset.trans hKu
    obtain ⟨B, hBmem, haB, hBV⟩ :=
      (TopologicalSpace.isBasis_countableBasis ↥W).exists_subset_of_mem_open haK
        isOpen_interior
    refine ⟨B, ⟨hBmem, ?_⟩, haB, hBV.trans hVsub⟩
    exact hVclosure.of_isClosed_subset isClosed_closure (closure_mono hBV)

/-- Finite unions from the compact basis have compact closure. -/
theorem isCompact_closure_biUnion (F : Finset ↥(compactBasis W)) :
    IsCompact (closure (⋃ b ∈ (↑F : Set ↥(compactBasis W)), b.val)) := by
  have hfin : (↑F : Set ↥(compactBasis W)).Finite := F.finite_toSet
  have hcov : closure (⋃ b ∈ (↑F : Set ↥(compactBasis W)), b.val) ⊆
      ⋃ b ∈ (↑F : Set ↥(compactBasis W)), closure b.val := by
    apply closure_minimal _ _
    · intro x hx
      obtain ⟨b, hb, hxb⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion₂.mpr ⟨b, hb, subset_closure hxb⟩
    · exact hfin.isClosed_biUnion (fun _ _ => isClosed_closure)
  exact (hfin.isCompact_biUnion (fun b _ => (b.2).2)).of_isClosed_subset
    isClosed_closure hcov

/-- A countable basis for `W⁺`: coercions plus complements of finite-union closures. -/
noncomputable def onePointBasis : Set (Set (OnePoint ↥W)) :=
  Set.image ((↑) : ↥W → OnePoint ↥W) '' (compactBasis W) ∪
    (fun F : Finset ↥(compactBasis W) =>
      (((↑) '' (closure (⋃ b ∈ (↑F : Set ↥(compactBasis W)), b.val))) :
        Set (OnePoint ↥W))ᶜ) '' univ

theorem countable_onePointBasis : (onePointBasis W).Countable := by
  have h1 : (Set.image ((↑) : ↥W → OnePoint ↥W) '' (compactBasis W)).Countable :=
    (countable_compactBasis W).image _
  have _c : Countable ↥(compactBasis W) := countable_compactBasis W
  have h2 : ((fun F : Finset ↥(compactBasis W) =>
      (((↑) '' (closure (⋃ b ∈ (↑F : Set ↥(compactBasis W)), b.val))) :
        Set (OnePoint ↥W))ᶜ) '' univ).Countable :=
    Set.countable_univ.image _
  exact h1.union h2

theorem isBasis_onePointBasis (hW : IsOpen W) :
    TopologicalSpace.IsTopologicalBasis (onePointBasis W) := by
  have _lc := locallyCompactSpace_coe W hW
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  · intro v hv
    simp only [onePointBasis, Set.mem_union, Set.mem_image] at hv
    rcases hv with ⟨U, hU, rfl⟩ | ⟨F, -, rfl⟩
    · rw [isOpen_image_coe]
      exact (isBasis_compactBasis W hW).isOpen hU
    · rw [isOpen_compl_image_coe]
      exact ⟨isClosed_closure, isCompact_closure_biUnion W F⟩
  · intro a u hau hu
    induction a using OnePoint.rec with
    | infty =>
      rw [isOpen_iff_of_mem hau] at hu
      obtain ⟨hclosed, hcompact⟩ := hu
      set t : Set ↥W := ((↑) : ↥W → OnePoint ↥W) ⁻¹' u with ht
      have hUo : ∀ i : ↥(compactBasis W), IsOpen i.val :=
        fun i => (isBasis_compactBasis W hW).isOpen i.2
      have hsU : tᶜ ⊆ ⋃ i : ↥(compactBasis W), i.val := by
        intro x _
        obtain ⟨B, hB, hxB, -⟩ :=
          (isBasis_compactBasis W hW).exists_subset_of_mem_open (Set.mem_univ x)
            isOpen_univ
        exact Set.mem_iUnion.mpr ⟨⟨B, hB⟩, hxB⟩
      obtain ⟨F, hFsub⟩ := hcompact.elim_finite_subcover _ hUo hsU
      refine ⟨_, Or.inr ⟨F, Set.mem_univ F, rfl⟩, infty_notMem_image_coe, ?_⟩
      intro y hy
      induction y using OnePoint.rec with
      | infty => exact hau
      | coe w =>
        have hw : w ∉ closure (⋃ i ∈ (↑F : Set ↥(compactBasis W)), i.val) := by
          intro hcon
          exact hy ⟨w, hcon, rfl⟩
        have hw' : w ∉ ⋃ i ∈ (↑F : Set ↥(compactBasis W)), i.val :=
          fun hcon => hw (subset_closure hcon)
        have hw'' : w ∉ tᶜ := fun hcon => hw' (hFsub hcon)
        have hwt : w ∈ t := Classical.byContradiction fun h => hw'' h
        exact hwt
    | coe w =>
      have htopen : IsOpen (((↑) : ↥W → OnePoint ↥W) ⁻¹' u) :=
        OnePoint.continuous_coe.isOpen_preimage _ hu
      obtain ⟨B, hB, hwB, hBt⟩ :=
        (isBasis_compactBasis W hW).exists_subset_of_mem_open hau htopen
      refine ⟨_, Or.inl ⟨B, hB, rfl⟩, ⟨w, hwB, rfl⟩, ?_⟩
      rintro y ⟨v, hvB, rfl⟩
      exact hBt hvB

/-- The one-point compactification of an open subset of `E` is second countable. -/
theorem secondCountableTopology_onePoint (hW : IsOpen W) :
    SecondCountableTopology (OnePoint ↥W) :=
  TopologicalSpace.IsTopologicalBasis.secondCountableTopology
    (isBasis_onePointBasis W hW) (countable_onePointBasis W)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- `W⁺` is compact. -/
theorem compactSpace_onePoint : CompactSpace (OnePoint ↥W) := inferInstance

/-- `W⁺` is compact metrizable. -/
theorem metrizableSpace_onePoint (hW : IsOpen W) :
    TopologicalSpace.MetrizableSpace (OnePoint ↥W) := by
  have _lc := locallyCompactSpace_coe W hW
  have _sc := secondCountableTopology_onePoint W hW
  exact inferInstance

end SecondCountable

section Action

variable (W : Set E)
variable {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]
  [MulAction G ↥W] [ContinuousSMul G ↥W]

/-- The action extended to `W⁺`, fixing `∞`. -/
noncomputable def osmul (g : G) (x : OnePoint ↥W) : OnePoint ↥W :=
  x.elim ∞ (fun w => ↑(g • w))

noncomputable instance : SMul G (OnePoint ↥W) := ⟨osmul (G := G) W⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] [CompactSpace G] [ContinuousSMul G ↥W] in
@[simp] theorem osmul_infty (g : G) : g • (∞ : OnePoint ↥W) = ∞ := rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] [CompactSpace G] [ContinuousSMul G ↥W] in
@[simp] theorem osmul_coe (g : G) (w : ↥W) : g • (↑w : OnePoint ↥W) = ↑(g • w) := rfl

noncomputable instance : MulAction G (OnePoint ↥W) where
  one_smul x := by
    induction x using OnePoint.rec with
    | infty => rfl
    | coe w => simp [osmul_coe, one_smul]
  mul_smul g h x := by
    induction x using OnePoint.rec with
    | infty => rfl
    | coe w => simp [osmul_coe, mul_smul]

/-- Saturation of a set by the `G`-action. -/
noncomputable def saturate (K : Set ↥W) : Set ↥W :=
  (fun p : G × ↥W => p.1 • p.2) '' (Set.univ ×ˢ K)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem isCompact_saturate {K : Set ↥W} (hK : IsCompact K) :
    IsCompact (saturate (G := G) W K) :=
  (isCompact_univ.prod hK).image continuous_smul

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] [CompactSpace G] [ContinuousSMul G ↥W] in
theorem saturate_mem_of_mem {K : Set ↥W} {g : G} {w : ↥W} (hw : g • w ∈ K) :
    w ∈ saturate (G := G) W K := by
  have : w = g⁻¹ • (g • w) := (inv_smul_smul g w).symm
  rw [this]
  exact Set.mem_image_of_mem (fun p : G × ↥W => p.1 • p.2)
    (show (g⁻¹, g • w) ∈ Set.univ ×ˢ K from ⟨Set.mem_univ _, hw⟩)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] [CompactSpace G] [ContinuousSMul G ↥W] in
/-- Every group element maps `W⁺ ∖ GK` into `W⁺ ∖ K`. -/
theorem smul_mem_of_mem_saturate_compl {K : Set ↥W} {g : G} {w : ↥W}
    (hw : w ∉ saturate (G := G) W K) : g • w ∉ K :=
  fun hmem => hw (saturate_mem_of_mem W hmem)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The extended action is jointly continuous. -/
theorem continuousSMul_onePoint :
    ContinuousSMul G (OnePoint ↥W) where
  continuous_smul := by
    rw [continuous_def]
    intro s hs
    have hφ : IsOpenMap (Prod.map (id : G → G) ((↑) : ↥W → OnePoint ↥W)) :=
      IsOpenMap.prodMap IsOpenMap.id OnePoint.isOpenMap_coe
    by_cases hmem : ∞ ∈ s
    · rw [isOpen_iff_of_mem hmem] at hs
      obtain ⟨hclosed, hcompact⟩ := hs
      set t : Set ↥W := ((↑) : ↥W → OnePoint ↥W) ⁻¹' s with ht
      have htopen : IsOpen t := by simpa using isOpen_compl_iff.mpr hclosed
      have hGK : IsCompact (saturate (G := G) W tᶜ) := isCompact_saturate W hcompact
      have hGKclosed : IsClosed (saturate (G := G) W tᶜ) := hGK.isClosed
      have hunion : (fun p : G × OnePoint ↥W => p.1 • p.2) ⁻¹' s =
          Prod.map id ((↑) : ↥W → OnePoint ↥W) '' ((fun p : G × ↥W => p.1 • p.2) ⁻¹' t) ∪
          (Set.univ ×ˢ (((↑) '' (saturate (G := G) W tᶜ))ᶜ : Set (OnePoint ↥W))) := by
        ext ⟨g, x⟩
        induction x using OnePoint.rec with
        | infty =>
          simp only [Set.mem_preimage, osmul_infty]
          constructor
          · intro _
            right
            exact ⟨Set.mem_univ g, infty_notMem_image_coe⟩
          · rintro (⟨⟨g', w'⟩, -, heq⟩ | -)
            · have heq2 : (↑w' : OnePoint ↥W) = ∞ := congrArg Prod.snd heq
              exact (OnePoint.coe_ne_infty w' heq2).elim
            · exact hmem
        | coe w =>
          simp only [Set.mem_preimage, osmul_coe]
          constructor
          · intro hmem'
            by_cases hw : w ∈ saturate (G := G) W tᶜ
            · left; exact ⟨(g, w), hmem', rfl⟩
            · right
              rw [Set.mem_prod]
              refine ⟨Set.mem_univ g, ?_⟩
              rintro hcon
              obtain ⟨v, hvmem, heq⟩ := hcon
              have hvw : v = w := OnePoint.coe_injective heq
              subst hvw
              exact hw hvmem
          · rintro (⟨⟨g', w'⟩, hmem', heq⟩ | hmem')
            · have heq1 : g' = g := congrArg Prod.fst heq
              have heq2 : (↑w' : OnePoint ↥W) = ↑w := congrArg Prod.snd heq
              have hww : w' = w := OnePoint.coe_injective heq2
              subst heq1; subst hww
              exact hmem'
            · rw [Set.mem_prod] at hmem'
              have hw : w ∉ saturate (G := G) W tᶜ := fun hcon =>
                hmem'.2 ⟨w, hcon, rfl⟩
              by_contra hcon
              have hcon' : g • w ∈ tᶜ := hcon
              exact smul_mem_of_mem_saturate_compl W hw hcon'
      rw [hunion]
      refine IsOpen.union (hφ _ ?_) (isOpen_univ.prod ?_)
      · exact continuous_smul.isOpen_preimage _ htopen
      · exact isOpen_compl_image_coe.mpr ⟨hGKclosed, hGK⟩
    · rw [isOpen_iff_of_notMem hmem] at hs
      set t : Set ↥W := ((↑) : ↥W → OnePoint ↥W) ⁻¹' s with ht
      have hunion : (fun p : G × OnePoint ↥W => p.1 • p.2) ⁻¹' s =
          Prod.map id ((↑) : ↥W → OnePoint ↥W) '' ((fun p : G × ↥W => p.1 • p.2) ⁻¹' t) := by
        ext ⟨g, x⟩
        induction x using OnePoint.rec with
        | infty =>
          simp only [Set.mem_preimage, osmul_infty, Set.mem_image]
          constructor
          · intro hcon; exact absurd hcon hmem
          · rintro ⟨⟨g', w'⟩, -, heq⟩
            have heq2 : (↑w' : OnePoint ↥W) = ∞ := congrArg Prod.snd heq
            exact (OnePoint.coe_ne_infty w' heq2).elim
        | coe w =>
          simp only [Set.mem_preimage, osmul_coe, Set.mem_image]
          constructor
          · intro hmem'
            exact ⟨(g, w), hmem', rfl⟩
          · rintro ⟨⟨g', w'⟩, hmem', heq⟩
            have heq1 : g' = g := congrArg Prod.fst heq
            have heq2 : (↑w' : OnePoint ↥W) = ↑w := congrArg Prod.snd heq
            have hww : w' = w := OnePoint.coe_injective heq2
            subst heq1; subst hww
            exact hmem'
      rw [hunion]
      exact hφ _ (continuous_smul.isOpen_preimage _ hs)

/-- The extended action as an instance. -/
noncomputable instance : ContinuousSMul G (OnePoint ↥W) := continuousSMul_onePoint W

section Orbit

variable (H : Subgroup G)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] [CompactSpace G] [ContinuousSMul G ↥W] in
/-- The orbit relation set is the continuous image of `H × W⁺`. -/
theorem orbitRel_eq_image :
    {q : OnePoint ↥W × OnePoint ↥W |
        (Quotient.mk (MulAction.orbitRel H (OnePoint ↥W))) q.1 =
        (Quotient.mk (MulAction.orbitRel H (OnePoint ↥W))) q.2} =
    (fun p : H × OnePoint ↥W => (p.1 • p.2, p.2)) '' univ := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_univ, true_and]
  rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨(h, y), rfl⟩
  · rintro ⟨⟨h, z⟩, heq⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    exact ⟨h, rfl⟩

/-- The orbit space by a closed subgroup of `G` is Hausdorff. -/
theorem t2Space_orbitQuotient (hW : IsOpen W) (hH : IsClosed (H : Set G)) :
    T2Space (Quotient (MulAction.orbitRel H (OnePoint ↥W))) := by
  have _lc := locallyCompactSpace_coe W hW
  have _t4 : T4Space (OnePoint ↥W) := inferInstance
  have _t2 : T2Space (OnePoint ↥W) := inferInstance
  rw [t2Space_iff_of_isOpenQuotientMap MulAction.isOpenQuotientMap_quotientMk]
  rw [orbitRel_eq_image W H]
  have _cH : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  exact (isCompact_univ.image (continuous_smul.prodMk continuous_snd)).isClosed

/-- The orbit space by a closed subgroup of `G` is compact metrizable. -/
theorem metrizableSpace_orbitQuotient (hW : IsOpen W) (hH : IsClosed (H : Set G)) :
    TopologicalSpace.MetrizableSpace
      (Quotient (MulAction.orbitRel H (OnePoint ↥W))) := by
  have _sc := secondCountableTopology_onePoint W hW
  have _scQ : SecondCountableTopology
      (Quotient (MulAction.orbitRel H (OnePoint ↥W))) :=
    ContinuousConstSMul.secondCountableTopology
  have _t2Q := t2Space_orbitQuotient W H hW hH
  exact inferInstance

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace G] [CompactSpace G]
  [ContinuousSMul G ↥W] in
/-- The orbit space is compact. -/
theorem compactSpace_orbitQuotient :
    CompactSpace (Quotient (MulAction.orbitRel H (OnePoint ↥W))) := inferInstance

end Orbit

end Action



end HilbertSmith
