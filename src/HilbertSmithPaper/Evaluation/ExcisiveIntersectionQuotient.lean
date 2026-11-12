import HilbertSmithPaper.Categories.Supports.RelativeIntersectionAdditive
import HilbertSmithPaper.Categories.Supports.SupportFiltration
import HilbertSmithPaper.LTheory.Base.Categories.QuotientDualityFunctor
import HilbertSmithPaper.LTheory.Base.Categories.QuotientDualLift

/-!
# Quotient of an excisive intersection

Let `S, A, B, C ⊆ X` with `A` compact, `B` closed, `A ⊆ S` and `A ∩ B = C`. Inside `𝒜_S`, let
`𝒰_A` and `𝒰_B` be the `A`- and `B`-supported objects. The functors
`𝒰_A/(𝒰_A ∩ 𝒰_B) → 𝒜_A/𝒜_C` and `𝒜_A/𝒜_C → 𝒰_A/(𝒰_A ∩ 𝒰_B)`, `M ↦ M`, `[u] ↦ [u]`, are mutually
inverse strict duality functors (`HSP.excisiveInterQuotIso`).

* Forward: an object of `𝒰_A ∩ 𝒰_B` is `C`-supported, since for `ε > 0` there is `δ > 0` with
  `N_δ(A) ∩ N_δ(B) ⊆ N_ε(A ∩ B)`: take `δ ≤ ε/2` with disjoint `δ`-thickenings of the compact set
  `A \ N_{ε/2}(A ∩ B)` and of `B`. Nothing special happens for `A = ∅` or `B = ∅`.
* Backward: a `C`-supported object of `𝒜_A` is `B`-supported (`C ⊆ B`), and every object of
  `𝒜_A` is `S`-supported (`A ⊆ S`).

## Encoding

The isomorphism is a subtype of pairs `(e, e')` of duality functors, as for the quotient by the
empty support: `e` and `e'` are characterized on representatives by `q ⋙ e = ι ⋙ q` and
`q ⋙ e' = ι' ⋙ q`, both are strict, and both composites are identity functors. The intersection is
`C` with `A ∩ B = C` an equation hypothesis, so that the disjoint case takes `C = ∅` without a
transport. Compactness of `A` (rather than of `X`) is what the thickening argument uses.

## Kernel cost

Objects of `𝒜_A` and of `𝒜_S` are structures over the same objects of `𝒜_𝐆(X)` with proofs of
different support predicates. A kernel comparison of an object of `𝒜_A` with one of `𝒜_S` (both
reducing to the same underlying object) can first compare the two structures, and then fails only
after unfolding the support predicates down to metric thickenings, several seconds each. So the
inclusions `𝒰_A ⇄ 𝒜_A`, their duality structures and their composites are built for arbitrary
predicates `P`, `Q` and `R` (where such a comparison fails at once) and then instantiated, the
functors on the quotients are `FiltQuot.liftDual`, and support proofs are stated through `show`
at the inclusion functors.
-/

open CategoryTheory CategoryTheory.Limits Filter Metric

namespace HSP

open DualCat

section Generic

variable {D : Type*} [Category D] [Preadditive D] [Linear ℚ D] [HasFiniteBiproducts D]
  [DualCat D] {P Q : ObjectProperty D} [IsDualAdditive P] [IsDualAdditive Q]
  {R : ObjectProperty Q.FullSubcategory} [IsDualAdditive R]

private instance (h : ∀ X : R.FullSubcategory, P X.obj.obj) :
    (P.lift (R.ι ⋙ Q.ι) h).Additive where
  map_add := ObjectProperty.hom_ext _ rfl

private instance (hPQ : ∀ X : P.FullSubcategory, Q X.obj)
    (hPR : ∀ X : P.FullSubcategory, R ((Q.lift P.ι hPQ).obj X)) :
    (R.lift (Q.lift P.ι hPQ) hPR).Additive where
  map_add := ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _ rfl)

/-- The inclusion of the `R`-objects of `Q` into `P`, `M ↦ M`, `u ↦ u`, a strict duality
functor. -/
private def liftOutDual (h : ∀ X : R.FullSubcategory, P X.obj.obj) :
    DualFunctor R.FullSubcategory P.FullSubcategory where
  toFunctor := P.lift (R.ι ⋙ Q.ι) h
  ξ _ := Iso.refl _
  ξ_natural _ :=
    (Category.comp_id _).trans ((ObjectProperty.hom_ext _ rfl).trans (Category.id_comp _).symm)
  ξ_dual _ := (dualHom_id _).trans ((eqToHom_refl _ _).symm.trans (Category.comp_id _).symm)

/-- The inclusion of `P` into the `R`-objects of `Q`, `M ↦ M`, `u ↦ u`, a strict duality
functor. -/
private def liftInDual (hPQ : ∀ X : P.FullSubcategory, Q X.obj)
    (hPR : ∀ X : P.FullSubcategory, R ((Q.lift P.ι hPQ).obj X)) :
    DualFunctor P.FullSubcategory R.FullSubcategory where
  toFunctor := R.lift (Q.lift P.ι hPQ) hPR
  ξ _ := Iso.refl _
  ξ_natural _ := (Category.comp_id _).trans
    ((ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _ rfl)).trans (Category.id_comp _).symm)
  ξ_dual _ := (dualHom_id _).trans ((eqToHom_refl _ _).symm.trans (Category.comp_id _).symm)

private theorem liftOutDual_isStrict (h : ∀ X : R.FullSubcategory, P X.obj.obj) :
    (liftOutDual h).IsStrict :=
  fun _ => ⟨rfl, rfl⟩

private theorem liftInDual_isStrict (hPQ : ∀ X : P.FullSubcategory, Q X.obj)
    (hPR : ∀ X : P.FullSubcategory, R ((Q.lift P.ι hPQ).obj X)) :
    (liftInDual hPQ hPR).IsStrict :=
  fun _ => ⟨rfl, rfl⟩

private theorem liftOut_liftIn (h : ∀ X : R.FullSubcategory, P X.obj.obj)
    (hPQ : ∀ X : P.FullSubcategory, Q X.obj)
    (hPR : ∀ X : P.FullSubcategory, R ((Q.lift P.ι hPQ).obj X)) :
    (liftOutDual h).toFunctor ⋙ (liftInDual hPQ hPR).toFunctor = 𝟭 _ :=
  rfl

private theorem liftIn_liftOut (h : ∀ X : R.FullSubcategory, P X.obj.obj)
    (hPQ : ∀ X : P.FullSubcategory, Q X.obj)
    (hPR : ∀ X : P.FullSubcategory, R ((Q.lift P.ι hPQ).obj X)) :
    (liftInDual hPQ hPR).toFunctor ⋙ (liftOutDual h).toFunctor = 𝟭 _ :=
  rfl

end Generic

section GenericQuot

variable {A B E : Type*} [Category A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A] [Category B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B] [DualCat B]
  [Category E] [Preadditive E] [Linear ℚ E] [HasFiniteBiproducts E] [DualCat E]

private theorem liftDual_isStrict {U : ObjectProperty A} [IsDualAdditive U]
    {F : DualFunctor A B}
    {H : ∀ (x y : A) (f₁ f₂ : x ⟶ y), FiltQuot.rel U f₁ f₂ →
      F.toFunctor.map f₁ = F.toFunctor.map f₂} (hF : F.IsStrict) :
    (FiltQuot.liftDual U F H).IsStrict :=
  fun M => hF M.as

private theorem comp_isStrict {F : DualFunctor A B} {G : DualFunctor B E}
    (hF : F.IsStrict) (hG : G.IsStrict) : (F.comp G).IsStrict := fun M => by
  obtain ⟨h₁, e₁⟩ := hF M
  obtain ⟨h₂, e₂⟩ := hG (F.toFunctor.obj M)
  refine ⟨(congrArg G.toFunctor.obj h₁).trans h₂, ?_⟩
  simp only [DualFunctor.comp_ξ, Iso.trans_hom, Functor.mapIso_hom, e₁, e₂, eqToHom_map,
    eqToHom_trans]
  rfl

end GenericQuot

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

section

variable {S A B C : Set X}

/-- For `A` compact and `B` closed, `N_δ(A) ∩ N_δ(B) ⊆ N_ε(A ∩ B)` for some `δ > 0`. -/
private theorem exists_thickening_inter (hA : IsCompact A) (hB : IsClosed B) {ε : ℝ}
    (hε : 0 < ε) : ∃ δ > 0, ∀ x ∈ thickening δ A, x ∈ thickening δ B →
      x ∈ thickening ε (A ∩ B) := by
  have hε2 : 0 < ε / 2 := half_pos hε
  have hK : Disjoint (A \ thickening (ε / 2) (A ∩ B)) B := Set.disjoint_left.2
    fun x hx hxB => hx.2 (self_subset_thickening hε2 _ ⟨hx.1, hxB⟩)
  obtain ⟨δ, hδ, hd⟩ := hK.exists_thickenings (hA.diff isOpen_thickening) hB
  refine ⟨min δ (ε / 2), lt_min hδ hε2, fun x hxA hxB => ?_⟩
  obtain ⟨a, ha, hxa⟩ := mem_thickening_iff.1 hxA
  by_cases haC : a ∈ thickening (ε / 2) (A ∩ B)
  · obtain ⟨c, hc, hac⟩ := mem_thickening_iff.1 haC
    refine mem_thickening_iff.2 ⟨c, hc, ?_⟩
    calc dist x c ≤ dist x a + dist a c := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hxa.trans_le (min_le_right _ _)) hac
      _ = ε := add_halves ε
  · exact (Set.disjoint_left.1 hd
      (mem_thickening_iff.2 ⟨a, ⟨ha, haC⟩, hxa.trans_le (min_le_left _ _)⟩)
      (thickening_mono (min_le_left _ _) _ hxB)).elim

/-- An `A`- and `B`-supported object is `C`-supported, for `C = A ∩ B`. -/
private theorem supp_of_inter (hA : IsCompact A) (hB : IsClosed B) (hC : A ∩ B = C)
    {P : AsymCat G X} (hPA : supp A P) (hPB : supp B P) : supp C P := by
  subst hC
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := exists_thickening_inter hA hB hε
  filter_upwards [hPA δ hδ, hPB δ hδ] with i hi hi' k
  exact h _ (hi k) (hi' k)

/-- Supports are monotone. -/
private theorem supp_mono (h : A ⊆ S) {P : AsymCat G X} (hP : supp A P) : supp S P :=
  fun ε hε => (hP ε hε).mono fun _ hi k => thickening_subset_of_subset ε h (hi k)

variable (S A) in
/-- `𝒰_A → 𝒜_A`, `M ↦ M`, `u ↦ u`, as a strict duality functor. -/
private abbrev toSuppD :
    DualFunctor (suppIn (G := G) S A).FullSubcategory
      (supp A : ObjectProperty (AsymCat G X)).FullSubcategory :=
  liftOutDual (P := supp A) (Q := supp S) fun M => M.property

/-- `𝒜_A → 𝒰_A`, `M ↦ M`, `u ↦ u`, as a strict duality functor. -/
private abbrev toRelD (hAS : A ⊆ S) :
    DualFunctor (supp A : ObjectProperty (AsymCat G X)).FullSubcategory
      (suppIn (G := G) S A).FullSubcategory :=
  liftInDual (P := supp A) (Q := supp S)
    (fun M ε hε => (M.property ε hε).mono fun _ hi k => thickening_subset_of_subset ε hAS (hi k))
    fun M => show supp A ((supp A).ι.obj M) from M.property

private theorem toSupp_toRel (hAS : A ⊆ S) :
    (toSuppD (G := G) S A).toFunctor ⋙ (toRelD hAS).toFunctor = 𝟭 _ :=
  liftOut_liftIn _ _ _

private theorem toRel_toSupp (hAS : A ⊆ S) :
    (toRelD (G := G) hAS).toFunctor ⋙ (toSuppD S A).toFunctor = 𝟭 _ :=
  liftIn_liftOut _ _ _

private theorem fwd_compat (hA : IsCompact A) (hB : IsClosed B) (hC : A ∩ B = C)
    (x y : (suppIn (G := G) S A).FullSubcategory) (f₁ f₂ : x ⟶ y)
    (h : FiltQuot.rel (ExcisivePair.inter (suppIn S A) (suppIn S B)) f₁ f₂) :
    ((toSuppD S A).comp (FiltQuot.q (suppIn A C))).toFunctor.map f₁ =
      ((toSuppD S A).comp (FiltQuot.q (suppIn A C))).toFunctor.map f₂ := by
  obtain ⟨W, hW, a, b, hab⟩ := h
  rw [DualFunctor.comp_toFunctor, Functor.comp_map, Functor.comp_map]
  refine (FiltQuot.functor_map_eq_iff _ _ _).2 ⟨(toSuppD S A).toFunctor.obj W,
    show supp C (((suppIn S A).ι ⋙ (supp S).ι).obj W) from
      supp_of_inter hA hB hC W.property hW,
    (toSuppD S A).toFunctor.map a, (toSuppD S A).toFunctor.map b, ?_⟩
  rw [← Functor.map_sub, ← Functor.map_comp, hab]

private theorem bwd_compat (hAS : A ⊆ S) (hC : A ∩ B = C)
    (x y : (supp A : ObjectProperty (AsymCat G X)).FullSubcategory) (f₁ f₂ : x ⟶ y)
    (h : FiltQuot.rel (suppIn A C) f₁ f₂) :
    ((toRelD hAS).comp (FiltQuot.q (ExcisivePair.inter (suppIn S A) (suppIn S B)))).toFunctor.map
        f₁ =
      ((toRelD hAS).comp
        (FiltQuot.q (ExcisivePair.inter (suppIn S A) (suppIn S B)))).toFunctor.map f₂ := by
  obtain ⟨W, hW, a, b, hab⟩ := h
  rw [DualFunctor.comp_toFunctor, Functor.comp_map, Functor.comp_map]
  have hCB : C ⊆ B := hC ▸ Set.inter_subset_right
  refine (FiltQuot.functor_map_eq_iff _ _ _).2 ⟨(toRelD hAS).toFunctor.obj W,
    show supp B ((supp A).ι.obj W) from supp_mono hCB hW,
    (toRelD hAS).toFunctor.map a, (toRelD hAS).toFunctor.map b, ?_⟩
  rw [← Functor.map_sub, ← Functor.map_comp, hab]

variable (B) in
/-- `𝒰_A/(𝒰_A ∩ 𝒰_B) → 𝒜_A/𝒜_C`, `[u] ↦ [u]`. -/
private noncomputable def fwdD (hA : IsCompact A) (hB : IsClosed B) (hC : A ∩ B = C) :
    DualFunctor (FiltQuot (ExcisivePair.inter (suppIn (G := G) S A) (suppIn S B)))
      (FiltQuot (suppIn (G := G) A C)) :=
  FiltQuot.liftDual _ ((toSuppD S A).comp (FiltQuot.q _)) (fwd_compat hA hB hC)

/-- `𝒜_A/𝒜_C → 𝒰_A/(𝒰_A ∩ 𝒰_B)`, `[u] ↦ [u]`. -/
private noncomputable def bwdD (hAS : A ⊆ S) (hC : A ∩ B = C) :
    DualFunctor (FiltQuot (suppIn (G := G) A C))
      (FiltQuot (ExcisivePair.inter (suppIn (G := G) S A) (suppIn S B))) :=
  FiltQuot.liftDual _ ((toRelD hAS).comp (FiltQuot.q _)) (bwd_compat hAS hC)

private theorem fwd_spec (hA : IsCompact A) (hB : IsClosed B) (hC : A ∩ B = C) :
    CategoryTheory.Quotient.functor (FiltQuot.rel (ExcisivePair.inter (suppIn S A) (suppIn S B))) ⋙
        (fwdD (G := G) B hA hB hC).toFunctor =
      (toSuppD S A).toFunctor ⋙ FiltQuot.functor (suppIn A C) :=
  FiltQuot.liftDual_spec _ _ _

private theorem bwd_spec (hAS : A ⊆ S) (hC : A ∩ B = C) :
    CategoryTheory.Quotient.functor (FiltQuot.rel (suppIn A C)) ⋙
        (bwdD (G := G) hAS hC).toFunctor =
      (toRelD hAS).toFunctor ⋙
        FiltQuot.functor (ExcisivePair.inter (suppIn S A) (suppIn S B)) :=
  FiltQuot.liftDual_spec _ _ _

private theorem fwd_bwd (hA : IsCompact A) (hB : IsClosed B) (hAS : A ⊆ S) (hC : A ∩ B = C) :
    (fwdD (G := G) B hA hB hC).toFunctor ⋙ (bwdD hAS hC).toFunctor = 𝟭 _ :=
  CategoryTheory.Quotient.lift_unique' _ _ _ (by
    rw [← Functor.assoc, fwd_spec, Functor.assoc, bwd_spec, ← Functor.assoc, toSupp_toRel,
      Functor.id_comp, Functor.comp_id])

private theorem bwd_fwd (hA : IsCompact A) (hB : IsClosed B) (hAS : A ⊆ S) (hC : A ∩ B = C) :
    (bwdD (G := G) hAS hC).toFunctor ⋙ (fwdD B hA hB hC).toFunctor = 𝟭 _ :=
  CategoryTheory.Quotient.lift_unique' _ _ _ (by
    rw [← Functor.assoc, bwd_spec, Functor.assoc, fwd_spec, ← Functor.assoc, toRel_toSupp,
      Functor.id_comp, Functor.comp_id])

end

private theorem iso_prop (S : Set X) {A B C : Set X} (hA : IsCompact A)
    (hB : IsClosed B) (hAS : A ⊆ S) (hC : A ∩ B = C) :
    FiltQuot.functor _ ⋙ (fwdD (G := G) (S := S) B hA hB hC).toFunctor =
          ObjectProperty.lift _ ((suppIn S A).ι ⋙ (supp S).ι) (fun M => M.property) ⋙
            FiltQuot.functor _ ∧
        FiltQuot.functor _ ⋙ (bwdD (G := G) (B := B) hAS hC).toFunctor =
          ObjectProperty.lift _
            (ObjectProperty.lift _ (supp A).ι fun M ε hε => (M.property ε hε).mono
              fun _ hi k => thickening_subset_of_subset ε hAS (hi k))
            (fun M => show supp A ((supp A).ι.obj M) from M.property) ⋙
            FiltQuot.functor _ ∧
        (fwdD (G := G) (S := S) B hA hB hC).IsStrict ∧ (bwdD (G := G) (B := B) hAS hC).IsStrict ∧
        (fwdD (G := G) (S := S) B hA hB hC).toFunctor ⋙ (bwdD hAS hC).toFunctor = 𝟭 _ ∧
        (bwdD (G := G) (B := B) hAS hC).toFunctor ⋙ (fwdD B hA hB hC).toFunctor = 𝟭 _ :=
  ⟨fwd_spec hA hB hC, bwd_spec hAS hC,
    liftDual_isStrict (comp_isStrict (liftOutDual_isStrict _) (FiltQuot.q_isStrict _)),
    liftDual_isStrict (comp_isStrict (liftInDual_isStrict _ _) (FiltQuot.q_isStrict _)),
    fwd_bwd hA hB hAS hC, bwd_fwd hA hB hAS hC⟩

/-- **Quotient of an excisive intersection.** For `A` compact, `B` closed, `A ⊆ S` and
`A ∩ B = C`, the functors `e : 𝒰_A/(𝒰_A ∩ 𝒰_B) → 𝒜_A/𝒜_C` and `e' : 𝒜_A/𝒜_C → 𝒰_A/(𝒰_A ∩ 𝒰_B)`
induced by `M ↦ M`, `u ↦ u` (characterized by `q ⋙ e = ι ⋙ q` and `q ⋙ e' = ι' ⋙ q`) are
mutually inverse strict duality functors. -/
noncomputable def excisiveInterQuotIso (S : Set X) {A B C : Set X} (hA : IsCompact A)
    (hB : IsClosed B) (hAS : A ⊆ S) (hC : A ∩ B = C) :
    {e : DualFunctor (FiltQuot (ExcisivePair.inter (suppIn (G := G) S A) (suppIn S B)))
          (FiltQuot (suppIn (G := G) A C)) ×
        DualFunctor (FiltQuot (suppIn (G := G) A C))
          (FiltQuot (ExcisivePair.inter (suppIn (G := G) S A) (suppIn S B))) //
      FiltQuot.functor _ ⋙ e.1.toFunctor =
          ObjectProperty.lift _ ((suppIn S A).ι ⋙ (supp S).ι) (fun M => M.property) ⋙
            FiltQuot.functor _ ∧
        FiltQuot.functor _ ⋙ e.2.toFunctor =
          ObjectProperty.lift _
            (ObjectProperty.lift _ (supp A).ι fun M ε hε => (M.property ε hε).mono
              fun _ hi k => thickening_subset_of_subset ε hAS (hi k))
            (fun M => show supp A ((supp A).ι.obj M) from M.property) ⋙
            FiltQuot.functor _ ∧
        e.1.IsStrict ∧ e.2.IsStrict ∧ e.1.toFunctor ⋙ e.2.toFunctor = 𝟭 _ ∧
        e.2.toFunctor ⋙ e.1.toFunctor = 𝟭 _} :=
  ⟨(fwdD B hA hB hC, bwdD hAS hC), iso_prop S hA hB hAS hC⟩

end HSP
