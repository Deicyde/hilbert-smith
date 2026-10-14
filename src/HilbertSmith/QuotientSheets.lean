import Mathlib

open Set Topology Filter Function

namespace HilbertSmith

section Sheets

variable {G E : Type*} [Group G] [MulAction G E]

/-- At a point with trivial stabilizer, some open neighborhood meets each of its
nontrivial translates trivially. -/
theorem exists_open_disjoint_smul [TopologicalSpace E] [ContinuousConstSMul G E]
    [T2Space E] [LocallyCompactSpace E] [Finite G] {e : E}
    (he : MulAction.stabilizer G e = ⊥) :
    ∃ U : Set E, IsOpen U ∧ e ∈ U ∧
      ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1 := by
  obtain ⟨W, hWnhds, hW⟩ := ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self G e
  refine ⟨interior W, isOpen_interior, mem_interior_iff_mem_nhds.mpr hWnhds,
    fun g hg => ?_⟩
  have hgW : ((g • ·) '' W ∩ W).Nonempty :=
    hg.mono (Set.inter_subset_inter (Set.image_mono interior_subset) interior_subset)
  have hfix : g • e = e := hW g hgW
  have hmem : g ∈ MulAction.stabilizer G e := MulAction.mem_stabilizer_iff.mpr hfix
  rw [he, Subgroup.mem_bot] at hmem
  exact hmem

section SheetData

variable (U : Set E)

/-- The quotient map is constant on orbits. -/
private theorem quotient_smul (g : G) (u : E) :
    Quotient.mk (MulAction.orbitRel G E) (g • u)
      = Quotient.mk (MulAction.orbitRel G E) u :=
  Quotient.eq''.mpr ((MulAction.orbitRel_apply).mpr (MulAction.mem_orbit u g))

/-- Points identified by the quotient map lie on one orbit. -/
private theorem quotient_mem_orbit (w u : E)
    (h : Quotient.mk (MulAction.orbitRel G E) w = Quotient.mk (MulAction.orbitRel G E) u) :
    ∃ h : G, h • u = w :=
  MulAction.mem_orbit_iff.mp ((MulAction.orbitRel_apply).mp (Quotient.eq''.mp h))

/-- The `g`-sheet: the `g`-translate of `U`. -/
abbrev sheet (g : G) : Set E := (g • ·) '' U

/-- Sheets are open: translation is a homeomorphism. -/
theorem sheet_open [TopologicalSpace E] [ContinuousConstSMul G E]
    (hUopen : IsOpen U) (g : G) : IsOpen (sheet U g) := by
  have himg : (g • ·) '' U = (Homeomorph.smul (α := E) g) '' U := rfl
  rw [show sheet U g = (Homeomorph.smul (α := E) g) '' U from himg]
  exact (Homeomorph.smul (α := E) g).isOpen_image.mpr hUopen

/-- Distinct sheets are disjoint. -/
theorem sheet_pairwise_disjoint
    (hdisj : ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1) :
    Pairwise (Disjoint on (sheet (G := G) U)) := by
  intro c d hcd
  show Disjoint (sheet U c) (sheet U d)
  rw [Set.disjoint_left]
  rintro z ⟨u₁, hu₁U, rfl⟩ ⟨u₂, hu₂U, hEq⟩
  have hEq' : d • u₂ = c • u₁ := hEq
  have hcd1 : c⁻¹ * d = 1 :=
    hdisj (c⁻¹ * d) ⟨u₁, ⟨u₂, hu₂U, by
      show (c⁻¹ * d) • u₂ = u₁
      rw [mul_smul, hEq', inv_smul_smul]⟩, hu₁U⟩
  exact hcd (inv_mul_eq_one.mp hcd1)

/-- The sheets cover exactly the preimage of `V`. -/
theorem sheet_union :
    ⋃ (g : G), sheet U g
      = Quotient.mk (MulAction.orbitRel G E) ⁻¹'
        (Quotient.mk (MulAction.orbitRel G E) '' U) := by
  ext w
  simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_image]
  constructor
  · rintro ⟨g, u, huU, rfl⟩
    exact ⟨u, huU, (quotient_smul g u).symm⟩
  · rintro ⟨u, huU, hqu⟩
    obtain ⟨h, rfl⟩ := quotient_mem_orbit w u hqu.symm
    exact ⟨h, u, huU, rfl⟩

/-- `V` is open: its saturated preimage is a union of sheets. -/
theorem sheetImage_open [TopologicalSpace E] [ContinuousConstSMul G E]
    (hUopen : IsOpen U) :
    IsOpen (Quotient.mk (MulAction.orbitRel G E) '' U) := by
  have hq : IsQuotientMap (Quotient.mk (MulAction.orbitRel G E)) :=
    isQuotientMap_quotient_mk'
  rw [← IsCoinducing.isOpen_preimage hq.isCoinducing, (sheet_union U).symm]
  exact isOpen_iUnion fun g => sheet_open U hUopen g

/-- `V` is nonempty. -/
theorem sheetImage_nonempty {e : E} (heU : e ∈ U) :
    (Quotient.mk (MulAction.orbitRel G E) '' U).Nonempty :=
  ⟨Quotient.mk (MulAction.orbitRel G E) e, e, heU, rfl⟩

/-- Sheet points map into `V`. -/
private theorem sheet_mem_image (g : G) (x : E) (hx : x ∈ sheet U g) :
    Quotient.mk (MulAction.orbitRel G E) x
      ∈ Quotient.mk (MulAction.orbitRel G E) '' U := by
  obtain ⟨u, huU, huv⟩ := hx
  have huv' : g • u = x := huv
  exact ⟨u, huU, by rw [← huv']; exact (quotient_smul g u).symm⟩

/-- The quotient map restricted to a sheet, landing in `V`. -/
abbrev sheetMap (g : G) (x : ↥(sheet U g)) :
    ↥(Quotient.mk (MulAction.orbitRel G E) '' U) :=
  ⟨Quotient.mk (MulAction.orbitRel G E) x.1, sheet_mem_image U g x.1 x.2⟩

/-- Saturated preimages are unions of smul-images. -/
private theorem preimage_image_eq (A : Set E) :
    Quotient.mk (MulAction.orbitRel G E) ⁻¹'
        (Quotient.mk (MulAction.orbitRel G E) '' A)
      = ⋃ (h : G), (h • ·) '' A := by
  ext x
  simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
  constructor
  · rintro ⟨a, haA, haa⟩
    obtain ⟨h, rfl⟩ := quotient_mem_orbit x a haa.symm
    exact ⟨h, a, haA, rfl⟩
  · rintro ⟨h, a, haA, rfl⟩
    exact ⟨a, haA, (quotient_smul h a).symm⟩

/-- Smul by a group element is injective. -/
private theorem smul_injective (h : G) : Function.Injective ((h • ·) : E → E) := by
  intro a b hab
  have hab' : h • a = h • b := hab
  have h2 := congrArg (fun x => h⁻¹ • x) hab'
  have h2' : h⁻¹ • (h • a) = h⁻¹ • (h • b) := h2
  rwa [← mul_smul, ← mul_smul, inv_mul_cancel, one_smul, one_smul] at h2'

/-- Smul-images of an open set are open. -/
private theorem smul_image_open [TopologicalSpace E] [ContinuousConstSMul G E]
    (W : Set E) (hW : IsOpen W) (h : G) : IsOpen ((h • ·) '' W) := by
  have himg : (h • ·) '' W = (Homeomorph.smul (α := E) h) '' W := rfl
  rw [himg]
  exact (Homeomorph.smul (α := E) h).isOpen_image.mpr hW

/-- Smul-images of sheets are sheets. -/
private theorem sheet_smul_image (g h : G) :
    (h • ·) '' sheet U g = sheet U (h * g) := by
  ext y
  simp only [Set.mem_image]
  constructor
  · rintro ⟨x, ⟨u, huU, huv⟩, hxy⟩
    have huv' : g • u = x := huv
    have hxy' : h • x = y := hxy
    exact ⟨u, huU, by show (h * g) • u = y; rw [mul_smul, huv', hxy']⟩
  · rintro ⟨u, huU, huv⟩
    exact ⟨g • u, ⟨u, huU, rfl⟩, by show h • (g • u) = y; rw [← mul_smul]; exact huv⟩

/-- The image of a sheet-piece cut by an open set is open in `V`'s ambient. -/
private theorem image_inter_sheet_open [TopologicalSpace E] [ContinuousConstSMul G E]
    (hUopen : IsOpen U) (W' : Set E) (hW' : IsOpen W') (g : G) :
    IsOpen (Quotient.mk (MulAction.orbitRel G E) '' (W' ∩ sheet U g)) := by
  have hq : IsQuotientMap (Quotient.mk (MulAction.orbitRel G E)) :=
    isQuotientMap_quotient_mk'
  rw [← IsCoinducing.isOpen_preimage hq.isCoinducing, preimage_image_eq _]
  exact isOpen_iUnion fun h => by
    rw [Set.image_inter (smul_injective h), sheet_smul_image U g h]
    exact (smul_image_open W' hW' h).inter (sheet_open U hUopen (h * g))

/-- Each sheet maps homeomorphically onto `V`. -/
theorem sheet_homeomorph [TopologicalSpace E] [ContinuousConstSMul G E]
    (hUopen : IsOpen U)
    (hdisj : ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1) (g : G) :
    IsHomeomorph (sheetMap U g) := by
  refine ⟨?cont, ?isopen, ?bij⟩
  · exact Continuous.subtype_mk
      (continuous_quotient_mk'.comp continuous_subtype_val) _
  · intro T hT
    obtain ⟨W', hW'open, hTW'⟩ := isOpen_induced_iff.mp hT
    have himg : sheetMap U g '' T
        = Subtype.val ⁻¹' (Quotient.mk (MulAction.orbitRel G E) '' (W' ∩ sheet U g)) := by
      ext y
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨x, hxT, hxy⟩
        have hxW' : x.1 ∈ W' := by rw [← hTW'] at hxT; exact hxT
        have hxy' : Quotient.mk (MulAction.orbitRel G E) x.1 = y.1 :=
          congrArg Subtype.val hxy
        exact ⟨x.1, ⟨hxW', x.2⟩, hxy'⟩
      · rintro ⟨a, ⟨haW', haS⟩, hqy⟩
        refine ⟨⟨a, haS⟩, ?_, ?_⟩
        · rw [← hTW']; exact haW'
        · apply Subtype.ext; exact hqy
    rw [himg]
    exact (image_inter_sheet_open U hUopen W' hW'open g).preimage continuous_subtype_val
  · constructor
    · intro x y hxy
      obtain ⟨u₁, hu₁U, huv₁⟩ := x.2
      obtain ⟨u₂, hu₂U, huv₂⟩ := y.2
      have huv₁' : g • u₁ = x.1 := huv₁
      have huv₂' : g • u₂ = y.1 := huv₂
      have hq : Quotient.mk (MulAction.orbitRel G E) x.1
          = Quotient.mk (MulAction.orbitRel G E) y.1 := congrArg Subtype.val hxy
      obtain ⟨h, hhxy⟩ := quotient_mem_orbit x.1 y.1 hq
      have hcalc : (g⁻¹ * h * g) • u₂ = u₁ := by
        rw [mul_smul, mul_smul, huv₂', hhxy, ← huv₁', inv_smul_smul]
      have h1 : g⁻¹ * h * g = 1 :=
        hdisj (g⁻¹ * h * g) ⟨u₁, ⟨u₂, hu₂U, hcalc⟩, hu₁U⟩
      have hh1 : h = 1 := by
        have h2 := congrArg (fun k => g * k) h1
        have h2' : g * (g⁻¹ * h * g) = g * 1 := h2
        rw [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, mul_one] at h2'
        have h3 : h * g = 1 * g := by rw [one_mul]; exact h2'
        exact mul_right_cancel h3
      have hxy' : y.1 = x.1 := by rw [← hhxy, hh1, one_smul]
      exact Subtype.ext hxy'.symm
    · intro v
      obtain ⟨u, huU, huv⟩ := v.2
      refine ⟨⟨g • u, u, huU, rfl⟩, ?_⟩
      apply Subtype.ext
      show Quotient.mk (MulAction.orbitRel G E) (g • u) = v.1
      rw [quotient_smul]
      exact huv

/-- The full preimage of `V`: the domain of the test function. -/
abbrev fiberV : Set E :=
  Quotient.mk (MulAction.orbitRel G E) ⁻¹' (Quotient.mk (MulAction.orbitRel G E) '' U)

/-- Sheets are unique: a point lies on at most one sheet. -/
theorem sheet_unique (hdisj : ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1)
    {w : E} {a b : G} (ha : w ∈ sheet U a) (hb : w ∈ sheet U b) : a = b := by
  by_contra hne
  have hdis : Disjoint (sheet U a) (sheet U b) :=
    sheet_pairwise_disjoint U hdisj hne
  exact (Set.disjoint_left.mp hdis) ha hb

/-- Every point over `V` lies on some sheet. -/
theorem sheet_exists (w : ↥(fiberV (G := G) U)) : ∃ (g : G), w.1 ∈ sheet U g := by
  have hmem : w.1 ∈ ⋃ (g : G), sheet U g := by
    rw [sheet_union U]
    exact w.2
  exact Set.mem_iUnion.mp hmem

/-- The sheet coordinate of a point over `V`. -/
noncomputable def sheetCoord
    (_hdisj : ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1)
    (w : ↥(fiberV (G := G) U)) : G :=
  Classical.choose (sheet_exists U w)

/-- The coordinate picks a sheet containing the point. -/
theorem sheetCoord_mem (hdisj : ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1)
    (w : ↥(fiberV (G := G) U)) : w.1 ∈ sheet U (sheetCoord U hdisj w) :=
  Classical.choose_spec (sheet_exists U w)

/-- The coordinate is the unique sheet containing the point. -/
theorem sheetCoord_unique (hdisj : ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1)
    (w : ↥(fiberV (G := G) U)) {c : G} (hc : w.1 ∈ sheet U c) :
    sheetCoord U hdisj w = c :=
  sheet_unique U hdisj (sheetCoord_mem U hdisj w) hc

/-- Smul-translates stay over `V`. -/
theorem shift_mem (w : ↥(fiberV (G := G) U)) (k : G) : k • w.1 ∈ fiberV (G := G) U := by
  show Quotient.mk (MulAction.orbitRel G E) (k • w.1)
    ∈ Quotient.mk (MulAction.orbitRel G E) '' U
  rw [quotient_smul]
  exact w.2

/-- The coordinate shifts by left multiplication under smul. -/
theorem sheetCoord_shift (hdisj : ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1)
    (w : ↥(fiberV (G := G) U)) (k : G) (hw : k • w.1 ∈ fiberV (G := G) U) :
    sheetCoord U hdisj ⟨k • w.1, hw⟩ = k * sheetCoord U hdisj w := by
  apply sheetCoord_unique
  obtain ⟨u, huU, huv⟩ := sheetCoord_mem U hdisj w
  have huv' : sheetCoord U hdisj w • u = w.1 := huv
  exact ⟨u, huU, by
    show (k * sheetCoord U hdisj w) • u = k • w.1
    rw [mul_smul, huv']⟩

/-- The sheet coordinate is locally constant: fibers are open sheets. -/
theorem sheetCoord_locallyConstant [TopologicalSpace E] [ContinuousConstSMul G E]
    (hUopen : IsOpen U)
    (hdisj : ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1) :
    IsLocallyConstant (sheetCoord U hdisj) := by
  intro s
  have hfib : sheetCoord U hdisj ⁻¹' s
      = ⋃ (c : G) (_ : c ∈ s), Subtype.val ⁻¹' sheet U c := by
    ext y
    simp only [Set.mem_preimage, Set.mem_iUnion]
    constructor
    · intro hy
      exact ⟨sheetCoord U hdisj y, hy, sheetCoord_mem U hdisj y⟩
    · rintro ⟨c, hcs, hyc⟩
      rw [sheetCoord_unique U hdisj y hyc]
      exact hcs
  rw [hfib]
  exact isOpen_iUnion fun c => isOpen_iUnion fun _ =>
    (sheet_open U hUopen c).preimage continuous_subtype_val

/-- The test function: a character of the sheet coordinate. -/
noncomputable def sheetBeta (hdisj : ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1)
    (χ : G →* ℂ) (w : ↥(fiberV (G := G) U)) : ℂ :=
  χ (sheetCoord U hdisj w)

/-- The test function is locally constant. -/
theorem sheetBeta_locallyConstant [TopologicalSpace E] [ContinuousConstSMul G E]
    (hUopen : IsOpen U)
    (hdisj : ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1) (χ : G →* ℂ) :
    IsLocallyConstant (sheetBeta U hdisj χ) :=
  IsLocallyConstant.comp (sheetCoord_locallyConstant U hUopen hdisj) χ

/-- The test function is equivariant for the character. -/
theorem sheetBeta_equivariant
    (hdisj : ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1) (χ : G →* ℂ)
    (w : ↥(fiberV (G := G) U)) (k : G) (hw : k • w.1 ∈ fiberV (G := G) U) :
    sheetBeta U hdisj χ ⟨k • w.1, hw⟩ = χ k * sheetBeta U hdisj χ w := by
  show χ (sheetCoord U hdisj ⟨k • w.1, hw⟩) = χ k * χ (sheetCoord U hdisj w)
  rw [sheetCoord_shift U hdisj w k hw, map_mul]

end SheetData

end Sheets

section Cyclic

/-- Powers of `exp` distribute over natural multiples. -/
theorem exp_pow_nat (z : ℂ) (n : ℕ) : (Complex.exp z) ^ n = Complex.exp (n * z) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, ← Complex.exp_add]; congr 1; push_cast; ring

/-- The primitive `m`-th root of unity. -/
noncomputable abbrev zeta (m : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / (m : ℂ))

/-- `ζ ^ m = 1`. -/
theorem zeta_pow_eq_one (m : ℕ) (hm : m ≠ 0) : (zeta m) ^ m = 1 := by
  have hmC : ((m : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr hm
  rw [exp_pow_nat]
  have harg : (m : ℂ) * (2 * Real.pi * Complex.I / (m : ℂ))
      = 2 * Real.pi * Complex.I := by
    field_simp
  rw [harg]
  exact Complex.exp_two_pi_mul_I

/-- The standard character of the cyclic group: `g ↦ ζ ^ g.val`. -/
noncomputable def cyclicChar (m : ℕ) (hm : m ≠ 0) :
    Multiplicative (ZMod m) →* ℂ where
  toFun g := zeta m ^ g.toAdd.val
  map_one' := by
    show zeta m ^ (0 : ZMod m).val = 1
    rw [ZMod.val_zero, pow_zero]
  map_mul' a b := by
    have : NeZero m := ⟨hm⟩
    show zeta m ^ (a.toAdd + b.toAdd).val
      = zeta m ^ a.toAdd.val * zeta m ^ b.toAdd.val
    rw [ZMod.val_add, ← pow_add]
    conv_rhs => rw [← Nat.mod_add_div (a.toAdd.val + b.toAdd.val) m]
    rw [pow_add, pow_mul, zeta_pow_eq_one m hm, one_pow, mul_one]

/-- The cyclic group has `m` elements: there are `m` sheets. -/
theorem cyclic_card (m : ℕ) [NeZero m] :
    Fintype.card (Multiplicative (ZMod m)) = m := by
  have h : Fintype.card (Multiplicative (ZMod m)) = Fintype.card (ZMod m) :=
    Fintype.card_congr (Equiv.refl (ZMod m))
  rw [h]
  exact ZMod.card m

/-- The cyclic test function is equivariant with `ζ ^ ḡ` weights. -/
theorem sheetBeta_cyclic_equivariant (m : ℕ) (hm : m ≠ 0) {E : Type*}
    [TopologicalSpace E] [MulAction (Multiplicative (ZMod m)) E]
    (U : Set E)
    (hdisj : ∀ g : Multiplicative (ZMod m), ((g • ·) '' U ∩ U).Nonempty → g = 1)
    (w : ↥(fiberV (G := Multiplicative (ZMod m)) U))
    (k : Multiplicative (ZMod m)) (hw : k • w.1 ∈ fiberV (G := Multiplicative (ZMod m)) U) :
    sheetBeta (G := Multiplicative (ZMod m)) U hdisj (cyclicChar m hm) ⟨k • w.1, hw⟩
      = zeta m ^ k.toAdd.val
        * sheetBeta (G := Multiplicative (ZMod m)) U hdisj (cyclicChar m hm) w :=
  sheetBeta_equivariant (G := Multiplicative (ZMod m)) U hdisj (cyclicChar m hm) w k hw

/-- The cyclic test function takes values among `1, ζ, …, ζ ^ (m-1)`. -/
theorem sheetBeta_cyclic_mem (m : ℕ) (hm : m ≠ 0) {E : Type*}
    [TopologicalSpace E] [MulAction (Multiplicative (ZMod m)) E]
    (U : Set E)
    (hdisj : ∀ g : Multiplicative (ZMod m), ((g • ·) '' U ∩ U).Nonempty → g = 1)
    (w : ↥(fiberV (G := Multiplicative (ZMod m)) U)) :
    ∃ j, j < m ∧ sheetBeta (G := Multiplicative (ZMod m)) U hdisj (cyclicChar m hm) w
      = zeta m ^ j := by
  have : NeZero m := ⟨hm⟩
  refine ⟨(sheetCoord (G := Multiplicative (ZMod m)) U hdisj w).toAdd.val,
    ZMod.val_lt _, rfl⟩

end Cyclic

end HilbertSmith
