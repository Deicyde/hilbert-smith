import HilbertSmithPaper.Categories.Supports.SupportIdeal
import HilbertSmithPaper.LTheory.Base.Categories.KaroubiFiltration
import HilbertSmithPaper.LTheory.Base.Categories.DualSubcategory

/-!
# Support filtration

For `S, S' ⊆ X`, `𝒜_{S'} ⊂ 𝒜_S` is the predicate "`S'`-supported" on the objects of the duality
category `𝒜_S = (supp S).FullSubcategory` (`HSP.suppIn S S'`). It is a full additive subcategory
closed under duality for all `S, S'` (`HSP.isDualAdditive_suppIn`, an instance: the empty sequence,
the concatenation, `M^* = M`), so the quotient `𝒜_S/𝒜_{S'}` is defined.

If the action is isometric and `S'` is invariant, it is an involution-invariant Karoubi filtration
(`HSP.supp_karoubiFiltration`). The chosen decompositions of `M = (n_i, x_i)` are indexed by the
null sequences `r : ℕ → ℝ≥0`: the diagonal coordinate projection `p_r` onto the indices `k` with
`x_i(k) ∈ Metric.cthickening (r i) S'` (empty when `S' = ∅`). It splits through `M_{≤r}`
(`AsymPre.restrict`) by the coordinate inclusion and its transpose, and `1 - p_r` through the
complementary restriction `M_{>r}`. Neither closedness nor `S' ⊆ S` is used.
-/

open CategoryTheory CategoryTheory.Limits Filter Topology Metric
open scoped NNReal ENNReal

namespace HSP

open DualCat

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

/-- `𝒜_{S'} ⊂ 𝒜_S`: the `S'`-supported objects of `𝒜_S`. -/
abbrev suppIn (S S' : Set X) : ObjectProperty (supp S : ObjectProperty (AsymCat G X)).FullSubcategory :=
  fun V => supp S' V.obj

/-- The empty sequence is `S`-supported. -/
theorem supp_zero (S : Set X) : supp S (⟨AsymPre.zero⟩ : AsymCat G X) :=
  fun _ _ => Eventually.of_forall fun _ k => k.elim0

/-- The concatenation of two `S`-supported objects is `S`-supported. -/
theorem supp_sum {S : Set X} {P Q : AsymCat G X} (hP : supp S P) (hQ : supp S Q) :
    supp S (AsymCat.binaryBicone P Q).pt := by
  intro ε hε
  filter_upwards [hP ε hε, hQ ε hε] with i h1 h2 k
  change Fin.append (P.as.x i) (Q.as.x i) k ∈ _
  refine Fin.addCases (fun k => ?_) (fun k => ?_) k
  · rw [Fin.append_left]; exact h1 k
  · rw [Fin.append_right]; exact h2 k

private theorem isZero_full (S : Set X) :
    IsZero (⟨⟨AsymPre.zero⟩, supp_zero S⟩ : (supp S : ObjectProperty (AsymCat G X)).FullSubcategory) :=
  ⟨fun Y => ⟨⟨⟨ObjectProperty.homMk (AsymCat.isZero_zero.to_ Y.obj)⟩, fun _ =>
      ObjectProperty.hom_ext _ (AsymCat.isZero_zero.eq_of_src _ _)⟩⟩,
    fun Y => ⟨⟨⟨ObjectProperty.homMk (AsymCat.isZero_zero.from_ Y.obj)⟩, fun _ =>
      ObjectProperty.hom_ext _ (AsymCat.isZero_zero.eq_of_tgt _ _)⟩⟩⟩

/-- `𝒜_{S'} ⊂ 𝒜_S` is a full additive subcategory closed under duality. -/
instance isDualAdditive_suppIn (S S' : Set X) : IsDualAdditive (suppIn (G := G) S S') where
  exists_zero := ⟨⟨⟨AsymPre.zero⟩, supp_zero S⟩, supp_zero S', isZero_full S⟩
  exists_biprod {V W} hV hW := by
    let c := AsymCat.binaryBicone V.obj W.obj
    let b : BinaryBicone V W :=
      { pt := ⟨c.pt, supp_sum V.property W.property⟩
        fst := ObjectProperty.homMk c.fst
        snd := ObjectProperty.homMk c.snd
        inl := ObjectProperty.homMk c.inl
        inr := ObjectProperty.homMk c.inr
        inl_fst := ObjectProperty.hom_ext _ c.inl_fst
        inl_snd := ObjectProperty.hom_ext _ c.inl_snd
        inr_fst := ObjectProperty.hom_ext _ c.inr_fst
        inr_snd := ObjectProperty.hom_ext _ c.inr_snd }
    exact ⟨b, ⟨isBinaryBilimitOfTotal b
      (ObjectProperty.hom_ext _ (AsymCat.binaryBicone_total V.obj W.obj))⟩, supp_sum hV hW⟩
  dual_mem h := h

/-- The indices `k` with `x_i(k)` in the closed `r_i`-thickening of `S'`. -/
def nearIdx (S' : Set X) (M : AsymPre G X) (r : ℕ → ℝ≥0) : ∀ i, Fin (M.n i) → Prop :=
  fun i k => M.x i k ∈ cthickening (r i) S'

open scoped Classical in
/-- The chosen decomposition `p_r` of `M ∈ 𝒜_S`: the diagonal coordinate projection onto the
indices `k` with `x_i(k) ∈ cthickening r_i S'`. -/
noncomputable def suppSplit {S : Set X} (S' : Set X)
    (M : (supp S : ObjectProperty (AsymCat G X)).FullSubcategory) (r : ℕ → ℝ≥0) : M ⟶ M :=
  ObjectProperty.homMk (AsymCat.mkHom (M.obj.as.trunc (nearIdx S' M.obj.as r)))

/-- A restriction of an `S`-supported object is `S`-supported. -/
theorem supp_restrict {S : Set X} {M : AsymPre G X} (hM : supp S (⟨M⟩ : AsymCat G X))
    (P : ∀ i, Fin (M.n i) → Prop) : supp S (⟨M.restrict P⟩ : AsymCat G X) := fun ε hε =>
  (hM ε hε).mono fun _ h _ => h _

/-- The restriction `M_{≤r}` to the closed `r_i`-thickenings of `S'` is `S'`-supported if `r` is
null. -/
theorem supp_restrict_near {S' : Set X} {M : AsymPre G X} {r : ℕ → ℝ≥0}
    (hr : Tendsto r atTop (𝓝 0)) : supp S' (⟨M.restrict (nearIdx S' M r)⟩ : AsymCat G X) := by
  intro ε hε
  have h := (NNReal.tendsto_coe.2 hr).eventually (gt_mem_nhds hε)
  filter_upwards [h] with i hi k
  exact cthickening_subset_thickening' hε hi S' (AsymPre.restrictEmb_mem k)

omit [AddAction (ZMod p) X] in
/-- A null sequence bounding, eventually, the closed thickenings of `S'` containing the `x_i(k)`
with `Q i k`, provided that for every `ε > 0` these points are eventually `ε`-close to `S'`. -/
theorem exists_null_cthickening {M : AsymPre G X} (S' : Set X) (Q : ∀ i, Fin (M.n i) → Prop)
    (h : ∀ ε > 0, ∀ᶠ i in atTop, ∀ k, Q i k → M.x i k ∈ thickening ε S') :
    ∃ r : ℕ → ℝ≥0, Tendsto r atTop (𝓝 0) ∧
      ∀ᶠ i in atTop, ∀ k, Q i k → M.x i k ∈ cthickening (r i) S' := by
  classical
  let f : ℕ → ℝ≥0∞ := fun i =>
    Finset.univ.sup fun k => if Q i k then Metric.infEDist (M.x i k) S' else 0
  have hf : Tendsto f atTop (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    obtain ⟨δ, hδ0, hδε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hε
    filter_upwards [h δ (NNReal.coe_pos.2 (ENNReal.coe_pos.1 hδ0))] with i hi
    refine Finset.sup_le fun k _ => ?_
    split_ifs with hk
    · have := mem_thickening_iff_infEDist_lt.1 (hi k hk)
      rw [ENNReal.ofReal_coe_nnreal] at this
      exact (this.trans hδε).le
    · exact zero_le
  refine ⟨fun i => (f i).toNNReal, ?_, ?_⟩
  · have := (ENNReal.tendsto_toNNReal ENNReal.zero_ne_top).comp hf
    simpa [Function.comp_def] using this
  · filter_upwards [hf.eventually (gt_mem_nhds zero_lt_one)] with i hi k hk
    rw [mem_cthickening_iff, ENNReal.ofReal_coe_nnreal,
      ENNReal.coe_toNNReal (hi.trans ENNReal.one_lt_top).ne]
    refine le_trans (le_of_eq ?_) (Finset.le_sup (f := fun k =>
      if Q i k then Metric.infEDist (M.x i k) S' else 0) (Finset.mem_univ k))
    simp only [hk, ↓reduceIte]

variable [IsIsometricVAdd (ZMod p) X]

/-- Factorization through a split, rows: for `u : V → M` with `V` `S'`-supported, eventually every
row of `u_i` carrying a nonzero entry has its label in the closed `r_i`-thickening of `S'`, for
some null `r`. -/
private theorem exists_null_rows {S' : Set X} (hS' : ∀ c : ZMod p, ∀ x ∈ S', c +ᵥ x ∈ S')
    {V M : AsymPre G X} (hV : supp S' (⟨V⟩ : AsymCat G X)) (u : V ⟶ M) :
    ∃ r : ℕ → ℝ≥0, Tendsto r atTop (𝓝 0) ∧ ∀ᶠ i in atTop,
      ∀ a b, FreeCat.mat (AsymPre.coord u i) a b ≠ 0 → nearIdx S' M r i a.2 := by
  have hI : FiltQuot.ideal (supp S') (AsymCat.mkHom u) :=
    ⟨⟨V⟩, hV, 𝟙 _, AsymCat.mkHom u, (Category.id_comp _).symm⟩
  have h := (factorsThrough_supp_iff hS' u).1 hI
  obtain ⟨r, hr, hev⟩ := exists_null_cthickening S'
    (fun i k => ∃ (g : G.G i) (b : G.G i × Fin (V.n i)),
      FreeCat.mat (AsymPre.coord u i) (g, k) b ≠ 0) (fun ε hε => by
      filter_upwards [h ε hε] with i hi k hk
      obtain ⟨g, b, hgb⟩ := hk
      exact (vadd_mem_thickening_iff hS' _).1 (hi _ _ hgb).1)
  exact ⟨r, hr, hev.mono fun i hi a b hab => hi a.2 ⟨a.1, b, hab⟩⟩

omit [IsIsometricVAdd (ZMod p) X] in
private theorem homMk_comp {S : Set X} {A B C : (supp S : ObjectProperty (AsymCat G X)).FullSubcategory}
    (f : A.obj ⟶ B.obj) (g : B.obj ⟶ C.obj) :
    ObjectProperty.homMk f ≫ ObjectProperty.homMk g = ObjectProperty.homMk (f ≫ g) := rfl

omit [IsIsometricVAdd (ZMod p) X] in
private theorem suppSplit_comp {S S' : Set X}
    (M : (supp S : ObjectProperty (AsymCat G X)).FullSubcategory) {r r' : ℕ → ℝ≥0}
    (h : ∀ i, r i ≤ r' i) : suppSplit S' M r ≫ suppSplit S' M r' = suppSplit S' M r ∧
      suppSplit S' M r' ≫ suppSplit S' M r = suppSplit S' M r := by
  classical
  have hmono : ∀ i k, nearIdx S' M.obj.as r i k → nearIdx S' M.obj.as r' i k :=
    fun i k hk => cthickening_mono (NNReal.coe_le_coe.2 (h i)) S' hk
  constructor <;> refine ObjectProperty.hom_ext _ ?_ <;>
    simp only [suppSplit, homMk_comp, ObjectProperty.homMk_hom] <;>
    rw [← Functor.map_comp, AsymPre.trunc_comp_trunc] <;> congr 1 <;>
    exact AsymPre.trunc_congr _ _ fun i k => by have := hmono i k; tauto

omit [IsIsometricVAdd (ZMod p) X] in
private theorem dualHom_suppSplit {S S' : Set X}
    (M : (supp S : ObjectProperty (AsymCat G X)).FullSubcategory) (r : ℕ → ℝ≥0) :
    dualHom (suppSplit S' M r) = suppSplit S' M r := by
  classical
  refine ObjectProperty.hom_ext _ ?_
  change AsymCat.mkHom (AsymPre.transpose _) = _
  rw [AsymPre.transpose_trunc]
  rfl

omit [IsIsometricVAdd (ZMod p) X] in
private theorem asym_dualHom_dualHom {P Q : AsymCat G X} (f : P ⟶ Q) : dualHom (dualHom f) = f := by
  obtain ⟨u, rfl⟩ := AsymCat.mkHom_surjective f
  rw [AsymCat.dualHom_mkHom, AsymCat.dualHom_mkHom, AsymPre.transpose_transpose]

/-- **Support filtration.** For an isometric action and an invariant `S'`, `𝒜_{S'} ⊂ 𝒜_S` is an
involution-invariant Karoubi filtration, with the chosen decompositions `p_r` (`r` a null sequence
of nonnegative reals): the diagonal coordinate projection onto the indices `k` with `x_i(k)` in the
closed `r_i`-thickening of `S'`. -/
noncomputable def supp_karoubiFiltration (S : Set X) {S' : Set X}
    (hS' : ∀ c : ZMod p, ∀ x ∈ S', c +ᵥ x ∈ S') :
    KaroubiFiltration (suppIn (G := G) S S') where
  D M := Set.range fun r : {r : ℕ → ℝ≥0 // Tendsto r atTop (𝓝 0)} => suppSplit S' M r.1
  idem := by
    rintro M _ ⟨r, rfl⟩
    exact (suppSplit_comp M fun _ => le_rfl).1
  split := by
    classical
    rintro M _ ⟨⟨r, hr⟩, rfl⟩
    refine ⟨⟨⟨M.obj.as.restrict (nearIdx S' M.obj.as r)⟩, supp_restrict M.property _⟩,
      supp_restrict_near hr, ObjectProperty.homMk (AsymCat.mkHom (AsymPre.restrictInc _ _)),
      ObjectProperty.homMk (AsymCat.mkHom (AsymPre.restrictPro _ _)), ?_, ?_⟩
    · refine ObjectProperty.hom_ext _ ?_
      rw [homMk_comp, ObjectProperty.homMk_hom, ← Functor.map_comp,
        AsymPre.restrictInc_restrictPro, CategoryTheory.Functor.map_id]
      rfl
    · refine ObjectProperty.hom_ext _ ?_
      rw [homMk_comp, ObjectProperty.homMk_hom, ← Functor.map_comp,
        AsymPre.restrictPro_restrictInc]
      rfl
  split_compl := by
    classical
    rintro M _ ⟨⟨r, hr⟩, rfl⟩
    refine ⟨⟨⟨M.obj.as.restrict (fun i k => ¬nearIdx S' M.obj.as r i k)⟩,
      supp_restrict M.property _⟩, ObjectProperty.homMk (AsymCat.mkHom (AsymPre.restrictInc _ _)),
      ObjectProperty.homMk (AsymCat.mkHom (AsymPre.restrictPro _ _)), ?_, ?_⟩
    · refine ObjectProperty.hom_ext _ ?_
      rw [homMk_comp, ObjectProperty.homMk_hom, ← Functor.map_comp,
        AsymPre.restrictInc_restrictPro, CategoryTheory.Functor.map_id]
      rfl
    · refine ObjectProperty.hom_ext _ ?_
      rw [homMk_comp, ObjectProperty.homMk_hom, ← Functor.map_comp,
        AsymPre.restrictPro_restrictInc, AsymPre.trunc_not, Functor.map_sub,
        CategoryTheory.Functor.map_id]
      rfl
  nonempty M := ⟨_, ⟨fun _ => 0, tendsto_const_nhds⟩, rfl⟩
  directed := by
    rintro M _ _ ⟨⟨r, hr⟩, rfl⟩ ⟨⟨r', hr'⟩, rfl⟩
    refine ⟨_, ⟨⟨fun i => max (r i) (r' i), by simpa using hr.max hr'⟩, rfl⟩,
      suppSplit_comp M fun i => le_max_left _ _, suppSplit_comp M fun i => le_max_right _ _⟩
  factor_left := by
    classical
    intro V M g hV
    obtain ⟨u, hu⟩ := AsymCat.mkHom_surjective g.hom
    obtain ⟨r, hr, hev⟩ := exists_null_rows hS' hV u
    refine ⟨_, ⟨⟨r, hr⟩, rfl⟩, ObjectProperty.hom_ext _ ?_⟩
    show g.hom ≫ (suppSplit S' M r).hom = g.hom
    rw [← hu]
    exact AsymPre.mkHom_comp_trunc_eq _ _ u hev
  factor_right := by
    classical
    intro M V g hV
    obtain ⟨u, hu⟩ := AsymCat.mkHom_surjective g.hom
    obtain ⟨r, hr, hev⟩ := exists_null_rows hS' hV (AsymPre.transpose u)
    refine ⟨_, ⟨⟨r, hr⟩, rfl⟩, ObjectProperty.hom_ext _ ?_⟩
    show (suppSplit S' M r).hom ≫ g.hom = g.hom
    rw [← hu]
    have h := congrArg dualHom (AsymPre.mkHom_comp_trunc_eq _ _ (AsymPre.transpose u) hev)
    rw [dualHom_comp, AsymCat.dualHom_mkHom, AsymCat.dualHom_mkHom, AsymPre.transpose_trunc,
      AsymPre.transpose_transpose] at h
    exact h
  dual_mem_iff := by
    classical
    intro M q
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨r, (dualHom_suppSplit M r.1).symm⟩
    · rintro ⟨r, hr⟩
      refine ⟨r, ObjectProperty.hom_ext _ ?_⟩
      have h := congrArg (fun f => dualHom f.hom) hr
      change dualHom (AsymCat.mkHom _) = dualHom (dualHom q.hom) at h
      rw [asym_dualHom_dualHom, AsymCat.dualHom_mkHom] at h
      show (suppSplit S' M r.1).hom = q.hom
      rw [← h]
      exact congrArg AsymCat.mkHom (AsymPre.transpose_trunc _ _).symm

/-- The trivial action of `C_2` on a point (for the non-vacuity witness). -/
private abbrev unitAction : AddAction (ZMod 2) Unit where
  vadd _ x := x
  zero_vadd _ := rfl
  add_vadd _ _ _ := rfl

attribute [local instance] unitAction

/-- Non-vacuity: the support filtration of `𝒜_X ⊂ 𝒜_X` for `X` a point (trivial, isometric
action of `C_2`). -/
private noncomputable def supp_karoubiFiltration_unit :
    KaroubiFiltration (suppIn (G := GroupSeq.trivial 2) (Set.univ : Set Unit) Set.univ) :=
  letI : IsIsometricVAdd (ZMod 2) Unit := ⟨fun _ => isometry_subsingleton⟩
  supp_karoubiFiltration _ fun _ _ _ => Set.mem_univ _

end HSP
