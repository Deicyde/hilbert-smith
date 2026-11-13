import HilbertSmithPaper.Categories.Supports.Excision
import HilbertSmithPaper.LTheory.Base.Categories.DualityFunctors.StrictDualityFunctor
import HilbertSmithPaper.LTheory.Base.Categories.DualityFunctors.CompositeDualityFunctor
import HilbertSmithPaper.Categories.Supports.IteratedQuotient
import HilbertSmithPaper.Categories.Supports.QuotientSupportFiltration
import HilbertSmithPaper.Categories.Supports.SupportIntersection

/-!
# Cut square

Let the action be isometric, `A, B, Z ⊆ X` invariant, `S = A ∪ B` and `𝒬 = 𝒜_S/𝒜_Z`. The cut square
(`HSP.cutSquare`) is the excisive pair `(𝒰_A, 𝒰_B)` in `𝒬`, `𝒰_A = quotSupp S Z A` and
`𝒰_B = quotSupp S Z B`; for compact `X` and closed `A, B` its intersection is `𝒰_{A ∩ B}`.

* `𝒰_A, 𝒰_B` are filtrations of `𝒬` by the quotient support filtrations.
* `𝒰_A ∩ 𝒰_B ⊂ 𝒰_A` is a filtration: the functor `J : 𝒜_A/𝒜_Z → 𝒰_A`, the identity on objects
  and on representatives, is full, and the chosen decompositions are the images under `J` of those
  of the quotient support filtration of `𝒜_A/𝒜_Z` by its `B`-supported objects.
* `r = K ∘ r₀ ∘ I`, where `I : 𝒬/𝒰_B → 𝒜_S/𝒜_{B ∪ Z}` is the iterated quotient, `r₀` the inverse of
  the excision equivalence for `A` and `B ∪ Z`, and `K : 𝒰'_A/(𝒰'_A ∩ 𝒰'_{B ∪ Z}) → 𝒰_A/(𝒰_A ∩ 𝒰_B)`
  the identity on objects and on representatives. The unit and counit are the images of those of
  the excision equivalence under `K` and under the inverse of `I`.

Non-vacuity: the private `cutSquare_unit` is the cut square for `X` a point with the trivial action
of `C_2`, the trivial group sequence, `A = B = X` and `Z = ∅`.
-/

open CategoryTheory CategoryTheory.Limits Filter Metric

namespace HSP

open DualCat

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

/-! ### The functor `J` and the filtration `𝒰_A ∩ 𝒰_B ⊂ 𝒰_A`

`J` and the transport of filtrations along it are set up for arbitrary predicates `P ≤ Q` on
`𝒜_𝐆(X)` and then specialised to `P = supp A`, `Q = supp S`. (Stated for the concrete support
predicates, the kernel spends minutes comparing `supp A` with `supp (A ∪ B)` while checking these
proofs.) -/

section JGeneric

variable {P Q : ObjectProperty (AsymCat G X)} [IsDualAdditive P] [IsDualAdditive Q]

private instance (h : P ≤ Q) : (ObjectProperty.ιOfLE h).Additive where
  map_add := rfl

variable (Q) in
/-- The predicate `N ↦ Y(N)` on `Q/U`, as for `quotSupp`. -/
private abbrev gR (U : ObjectProperty Q.FullSubcategory) (Y : ObjectProperty (AsymCat G X)) :
    ObjectProperty (FiltQuot U) :=
  fun N => Y N.as.obj

omit [IsDualAdditive P] [IsDualAdditive Q] in
/-- A predicate of the underlying object of `M` holds for its image in `Q`. -/
private theorem obj_mem_of_le (hPQ : P ≤ Q) (W : ObjectProperty (AsymCat G X))
    (M : P.FullSubcategory) (hM : W M.obj) :
    W (⟨M.obj, hPQ _ M.property⟩ : Q.FullSubcategory).obj :=
  hM

variable {U' : ObjectProperty P.FullSubcategory} {U : ObjectProperty Q.FullSubcategory}
  [IsDualAdditive U'] [IsDualAdditive U] {R : ObjectProperty (AsymCat G X)}

variable (U) in
/-- `J₀ : P → (Q/U)_P`, `M ↦ ⟨M⟩`, `u ↦ [u]`. -/
private abbrev gJ₀ (hPQ : P ≤ Q) : P.FullSubcategory ⥤ (gR Q U P).FullSubcategory :=
  ObjectProperty.lift _ (ObjectProperty.ιOfLE hPQ ⋙ FiltQuot.functor U) (fun M => M.property)

omit [IsDualAdditive P] [IsDualAdditive U'] in
private theorem gJ₀_compat (hPQ : P ≤ Q)
    (hU : ∀ V : P.FullSubcategory, U' V → U ⟨V.obj, hPQ _ V.property⟩)
    (x y : P.FullSubcategory) (f₁ f₂ : x ⟶ y) (h : FiltQuot.rel U' f₁ f₂) :
    (gJ₀ U hPQ).map f₁ = (gJ₀ U hPQ).map f₂ := by
  refine ObjectProperty.hom_ext _ ?_
  change (FiltQuot.functor U).map ((ObjectProperty.ιOfLE hPQ).map f₁) =
    (FiltQuot.functor U).map ((ObjectProperty.ιOfLE hPQ).map f₂)
  rw [FiltQuot.functor_map_eq_iff]
  obtain ⟨W, hW, a, b, hab⟩ := h
  refine ⟨(ObjectProperty.ιOfLE hPQ).obj W, hU W hW, (ObjectProperty.ιOfLE _).map a,
    (ObjectProperty.ιOfLE _).map b, ?_⟩
  rw [← Functor.map_sub, ← Functor.map_comp, hab]

/-- `J : P/U' → (Q/U)_P`, the identity on objects and on representatives. -/
private abbrev gJ (hPQ : P ≤ Q) (hU : ∀ V : P.FullSubcategory, U' V → U ⟨V.obj, hPQ _ V.property⟩) :
    FiltQuot U' ⥤ (gR Q U P).FullSubcategory :=
  CategoryTheory.Quotient.lift _ (gJ₀ U hPQ) (gJ₀_compat hPQ hU)

omit [IsDualAdditive P] [IsDualAdditive U'] in
private theorem gJ_map (hPQ : P ≤ Q)
    (hU : ∀ V : P.FullSubcategory, U' V → U ⟨V.obj, hPQ _ V.property⟩)
    (x y : P.FullSubcategory) (f : x ⟶ y) :
    (gJ hPQ hU).map ((FiltQuot.functor _).map f) = (gJ₀ U hPQ).map f :=
  CategoryTheory.Quotient.lift_map_functor_map _ _ _ _

private instance (hPQ : P ≤ Q) (hU : ∀ V : P.FullSubcategory, U' V → U ⟨V.obj, hPQ _ V.property⟩)
    : (gJ hPQ hU).Additive where
  map_add {_ _ f g} := by
    obtain ⟨f, rfl⟩ := (FiltQuot.functor U').map_surjective f
    obtain ⟨g, rfl⟩ := (FiltQuot.functor U').map_surjective g
    rw [← Functor.map_add, gJ_map, gJ_map, gJ_map]
    exact ObjectProperty.hom_ext _
      ((ObjectProperty.ιOfLE hPQ ⋙ FiltQuot.functor U).map_add (f := f) (g := g))

private instance (hPQ : P ≤ Q) (hU : ∀ V : P.FullSubcategory, U' V → U ⟨V.obj, hPQ _ V.property⟩) :
    (gJ hPQ hU).Full where
  map_surjective {M N} f := by
    obtain ⟨g, hg⟩ := (FiltQuot.functor U).map_surjective f.hom
    refine ⟨(FiltQuot.functor _).map (ObjectProperty.homMk g.hom : M.as ⟶ N.as), ?_⟩
    rw [gJ_map]
    exact ObjectProperty.hom_ext _ hg

private theorem gJ_map_dualHom (hPQ : P ≤ Q)
    (hU : ∀ V : P.FullSubcategory, U' V → U ⟨V.obj, hPQ _ V.property⟩)
    [IsDualAdditive (gR Q U P)] {M N : FiltQuot U'} (f : M ⟶ N) :
    (gJ hPQ hU).map (dualHom f) = dualHom ((gJ hPQ hU).map f) := by
  obtain ⟨g, rfl⟩ := (FiltQuot.functor U').map_surjective f
  rw [FiltQuot.dualHom_map, gJ_map, gJ_map]
  rfl

variable [IsDualAdditive (gR Q U P)] [IsDualAdditive (gR Q U R)] [IsDualAdditive (gR P U' R)]

/-- `(Q/U)_P ∩ (Q/U)_Y` is a full additive subcategory of `(Q/U)_P` closed under duality: it
contains the images under `J` of the zero objects and biproducts of `Y`-supported objects of
`P/U'`. -/
private theorem gInter_isDualAdditive (hPQ : P ≤ Q)
    (hU : ∀ V : P.FullSubcategory, U' V → U ⟨V.obj, hPQ _ V.property⟩) :
    IsDualAdditive (ExcisivePair.inter (gR Q U P) (gR Q U R)) where
  exists_zero := by
    obtain ⟨W, hW, hWz⟩ := IsDualAdditive.exists_zero (U := gR P U' R)
    exact ⟨(gJ hPQ hU).obj W, hW, (gJ hPQ hU).map_isZero hWz⟩
  exists_biprod {V W} hV hW := by
    obtain ⟨c, ⟨hc⟩, hpt⟩ := IsDualAdditive.exists_biprod (U := gR P U' R)
      (V := ⟨⟨V.obj.as.obj, V.property⟩⟩) (W := ⟨⟨W.obj.as.obj, W.property⟩⟩) hV hW
    refine ⟨(gJ hPQ hU).mapBinaryBicone c, ⟨isBinaryBilimitOfTotal _ ?_⟩, hpt⟩
    have h := congrArg (gJ hPQ hU).map (IsBilimit.binary_total hc)
    rw [CategoryTheory.Functor.map_add, Functor.map_comp, Functor.map_comp,
      CategoryTheory.Functor.map_id] at h
    exact h
  dual_mem hV := IsDualAdditive.dual_mem (U := gR Q U R) hV

/-- The filtration of `(Q/U)_P` by `(Q/U)_P ∩ (Q/U)_Y`: the images under `J` of the chosen
decompositions of a filtration of `P/U'` by its `Y`-supported objects. -/
private noncomputable def gFiltY (hPQ : P ≤ Q)
    (hU : ∀ V : P.FullSubcategory, U' V → U ⟨V.obj, hPQ _ V.property⟩)
    [IsDualAdditive (ExcisivePair.inter (gR Q U P) (gR Q U R))]
    (K : KaroubiFiltration (gR P U' R)) :
    KaroubiFiltration (ExcisivePair.inter (gR Q U P) (gR Q U R)) where
  D V := (gJ hPQ hU).map '' K.D ⟨⟨V.obj.as.obj, V.property⟩⟩
  idem := by
    rintro M _ ⟨q, hq, rfl⟩
    rw [← Functor.map_comp, K.idem hq]
  split := by
    rintro M _ ⟨q, hq, rfl⟩
    obtain ⟨E, hE, i, r, h1, h2⟩ := K.split hq
    exact ⟨(gJ hPQ hU).obj E, hE, (gJ hPQ hU).map i, (gJ hPQ hU).map r,
      by rw [← Functor.map_comp, h1, CategoryTheory.Functor.map_id],
      by rw [← Functor.map_comp, h2]⟩
  split_compl := by
    rintro M _ ⟨q, hq, rfl⟩
    obtain ⟨E, i, r, h1, h2⟩ := K.split_compl hq
    exact ⟨(gJ hPQ hU).obj E, (gJ hPQ hU).map i, (gJ hPQ hU).map r,
      by rw [← Functor.map_comp, h1, CategoryTheory.Functor.map_id],
      by rw [← Functor.map_comp, h2, Functor.map_sub, CategoryTheory.Functor.map_id]; rfl⟩
  nonempty M := by
    obtain ⟨q, hq⟩ := K.nonempty ⟨⟨M.obj.as.obj, M.property⟩⟩
    exact ⟨_, q, hq, rfl⟩
  directed := by
    rintro M _ _ ⟨q, hq, rfl⟩ ⟨q', hq', rfl⟩
    obtain ⟨q'', hq'', ⟨h1, h2⟩, ⟨h3, h4⟩⟩ := K.directed hq hq'
    exact ⟨(gJ hPQ hU).map q'', ⟨q'', hq'', rfl⟩,
      ⟨by rw [← Functor.map_comp, h1], by rw [← Functor.map_comp, h2]⟩,
      ⟨by rw [← Functor.map_comp, h3], by rw [← Functor.map_comp, h4]⟩⟩
  factor_left {V M} g hV := by
    let g' : (⟨⟨V.obj.as.obj, V.property⟩⟩ : FiltQuot U') ⟶ ⟨⟨M.obj.as.obj, M.property⟩⟩ :=
      (gJ hPQ hU).preimage g
    obtain ⟨q, hq, h⟩ := K.factor_left g' hV
    refine ⟨(gJ hPQ hU).map q, ⟨q, hq, rfl⟩, ?_⟩
    have h' := congrArg (gJ hPQ hU).map h
    rwa [Functor.map_comp, Functor.map_preimage] at h'
  factor_right {M V} g hV := by
    let g' : (⟨⟨M.obj.as.obj, M.property⟩⟩ : FiltQuot U') ⟶ ⟨⟨V.obj.as.obj, V.property⟩⟩ :=
      (gJ hPQ hU).preimage g
    obtain ⟨q, hq, h⟩ := K.factor_right g' hV
    refine ⟨(gJ hPQ hU).map q, ⟨q, hq, rfl⟩, ?_⟩
    have h' := congrArg (gJ hPQ hU).map h
    rwa [Functor.map_comp, Functor.map_preimage] at h'
  dual_mem_iff {M} q := by
    constructor
    · rintro ⟨q₀, hq₀, rfl⟩
      exact ⟨(dualHom q₀ :), (K.dual_mem_iff q₀).1 hq₀, gJ_map_dualHom hPQ hU q₀⟩
    · rintro ⟨q₀, hq₀, hq⟩
      refine ⟨(dualHom q₀ :), (K.dual_mem_iff q₀).1 hq₀, ?_⟩
      rw [gJ_map_dualHom, hq, dualHom_dualHom]
      erw [eqToHom_refl, Category.id_comp, Category.comp_id]

end JGeneric

section

variable {A B Z : Set X}

private theorem supp_le_union : (supp A : ObjectProperty (AsymCat G X)) ≤ supp (A ∪ B) :=
  fun _ hM ε hε => (hM ε hε).mono fun _ hi k =>
    thickening_subset_of_subset ε Set.subset_union_left (hi k)

/-- `𝒰_A ∩ 𝒰_B` is a full additive subcategory of `𝒰_A` closed under duality: it contains the
images under `J : 𝒜_A/𝒜_Z → 𝒰_A` (the identity on objects and on representatives) of the zero
objects and biproducts of `B`-supported objects of `𝒜_A/𝒜_Z`. -/
private instance cutInter_isDualAdditive :
    IsDualAdditive (ExcisivePair.inter (quotSupp (G := G) (A ∪ B) Z A) (quotSupp (A ∪ B) Z B)) :=
  gInter_isDualAdditive (P := supp A) (Q := supp (A ∪ B)) (U' := suppIn A Z)
    (U := suppIn (A ∪ B) Z) (R := supp B) supp_le_union (obj_mem_of_le supp_le_union (supp Z))

variable [IsIsometricVAdd (ZMod p) X]

variable (Z) in
/-- `𝒰_A ∩ 𝒰_B ⊂ 𝒰_A` is a Karoubi filtration: the images under `J` of the chosen decompositions
of the quotient support filtration of `𝒜_A/𝒜_Z` by its `B`-supported objects. -/
private noncomputable def cutFiltY (hB : ∀ c : ZMod p, ∀ x ∈ B, c +ᵥ x ∈ B) :
    KaroubiFiltration
      (ExcisivePair.inter (quotSupp (G := G) (A ∪ B) Z A) (quotSupp (A ∪ B) Z B)) :=
  gFiltY (P := supp A) (Q := supp (A ∪ B)) (U' := suppIn A Z) (U := suppIn (A ∪ B) Z)
    (R := supp B) supp_le_union (obj_mem_of_le supp_le_union (supp Z))
    (quotSupp_karoubiFiltration A Z hB)

end

section Excisive

variable [IsIsometricVAdd (ZMod p) X] {A B Z : Set X}

/-- A map between `A`-supported objects of `𝒜_S`, `S ⊆ A ∪ B`, in the ideal of `𝒜_B` lies in the
ideal of `𝒰_A ∩ 𝒰_B`: the excision equivalence `e` has a unit isomorphism, so it is faithful. -/
private theorem ideal_inter_of_excision {S : Set X} (hS : S ⊆ A ∪ B)
    (hB : ∀ c : ZMod p, ∀ x ∈ B, c +ᵥ x ∈ B)
    {V W : (suppIn (G := G) S A).FullSubcategory} (g : V ⟶ W)
    (hg : FiltQuot.ideal (suppIn S B) g.hom) :
    FiltQuot.ideal (ExcisivePair.inter (suppIn S A) (suppIn S B)) g := by
  have he : (ExcisivePair.e (suppIn (G := G) S A) (suppIn S B)).toFunctor.map
      ((FiltQuot.functor _).map g) = 0 := by
    change (FiltQuot.functor (suppIn S B)).map g.hom = 0
    rw [← (FiltQuot.functor (suppIn S B)).map_zero V.obj W.obj]
    exact (FiltQuot.functor_map_eq_iff _ _ _).2 (by rw [sub_zero]; exact hg)
  have hn := ((excision S A B hS hB).2.1.iso.hom.naturality ((FiltQuot.functor _).map g))
  have h0 : (FiltQuot.functor _).map g ≫
      (excision S A B hS hB).2.1.iso.hom.app ((FiltQuot.functor _).obj W) = 0 := by
    refine hn.trans ?_
    have hc : ((ExcisivePair.e (suppIn (G := G) S A) (suppIn S B)).comp
        (excision S A B hS hB).1).toFunctor.map ((FiltQuot.functor _).map g) =
        (excision S A B hS hB).1.toFunctor.map
          ((ExcisivePair.e (suppIn (G := G) S A) (suppIn S B)).toFunctor.map
            ((FiltQuot.functor _).map g)) := rfl
    rw [hc, he, Functor.map_zero]
    exact Limits.comp_zero
  have hx : (FiltQuot.functor (ExcisivePair.inter (suppIn (G := G) S A) (suppIn S B))).map g =
      (FiltQuot.functor _).map 0 := by
    rw [Functor.map_zero]
    exact (cancel_mono ((excision S A B hS hB).2.1.iso.hom.app _)).1
      (h0.trans Limits.zero_comp.symm)
  have := (FiltQuot.functor_map_eq_iff _ _ _).1 hx
  rwa [sub_zero] at this

end Excisive

section Functors

variable [IsIsometricVAdd (ZMod p) X] {A B Z : Set X}

omit [IsIsometricVAdd (ZMod p) X] in
variable (A B Z) in
/-- `K₀ : 𝒰'_A → 𝒰_A`, `V ↦ ⟨V⟩`, `u ↦ [u]`, from the `A`-supported objects of `𝒜_S` to those of
`𝒬`. -/
private abbrev cutK₀ :
    (suppIn (G := G) (A ∪ B) A).FullSubcategory ⥤
      (quotSupp (G := G) (A ∪ B) Z A).FullSubcategory :=
  ObjectProperty.lift _ ((suppIn (A ∪ B) A).ι ⋙ FiltQuot.functor (suppIn (A ∪ B) Z))
    (fun V => V.property)

omit [IsIsometricVAdd (ZMod p) X] in
private instance : (cutK₀ (G := G) A B Z).Additive where
  map_add {_ _ f g} := ObjectProperty.hom_ext _
    (((suppIn (A ∪ B) A).ι ⋙ FiltQuot.functor (suppIn (A ∪ B) Z)).map_add (f := f) (g := g))

omit [IsIsometricVAdd (ZMod p) X] in
private instance : (cutK₀ (G := G) A B Z).Linear ℚ where
  map_smul {_ _} f c := ObjectProperty.hom_ext _
    (((suppIn (A ∪ B) A).ι ⋙ FiltQuot.functor (suppIn (A ∪ B) Z)).map_smul c f)

omit [IsIsometricVAdd (ZMod p) X] in
/-- The map `𝒜_S/𝒜_{B ∪ Z} → (𝒜_S/𝒜_Z)/𝒰_B` of the iterated quotient kills a map `u` of `𝒜_S`
with `[u] = 0`, so the class of `u` in `𝒬` lies in the ideal of `𝒰_B`. -/
private theorem ideal_quotSupp_of_ideal_union
    {M N : (supp (A ∪ B) : ObjectProperty (AsymCat G X)).FullSubcategory} (u : M ⟶ N)
    (hu : FiltQuot.ideal (suppIn (A ∪ B) (B ∪ Z)) u) :
    FiltQuot.ideal (quotSupp (A ∪ B) Z B) ((FiltQuot.functor (suppIn (A ∪ B) Z)).map u) := by
  have hq : (FiltQuot.functor (suppIn (A ∪ B) (B ∪ Z))).map u = 0 := by
    rw [← (FiltQuot.functor (suppIn (A ∪ B) (B ∪ Z))).map_zero M N]
    exact (FiltQuot.functor_map_eq_iff _ _ _).2 (by rw [sub_zero]; exact hu)
  have h := CategoryTheory.Functor.congr_hom
    (iteratedQuotient (G := G) (A ∪ B) B Z).2.2.2.2.2.2 u
  simp only [Functor.comp_map, hq, Functor.map_zero] at h
  erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id] at h
  have h' := (FiltQuot.functor_map_eq_iff (quotSupp (G := G) (A ∪ B) Z B) _ 0).1
    (h.symm.trans (Functor.map_zero _ _ _).symm)
  rwa [sub_zero] at h'

private theorem cutK₀_compat (hB : ∀ c : ZMod p, ∀ x ∈ B, c +ᵥ x ∈ B)
    (x y : (suppIn (G := G) (A ∪ B) A).FullSubcategory) (f₁ f₂ : x ⟶ y)
    (h : FiltQuot.rel (ExcisivePair.inter (suppIn (A ∪ B) A) (suppIn (A ∪ B) (B ∪ Z))) f₁ f₂) :
    (cutK₀ A B Z ⋙ FiltQuot.functor
        (ExcisivePair.inter (quotSupp (A ∪ B) Z A) (quotSupp (A ∪ B) Z B))).map f₁ =
      (cutK₀ A B Z ⋙ FiltQuot.functor _).map f₂ := by
  change (FiltQuot.functor _).map ((cutK₀ A B Z).map f₁) =
    (FiltQuot.functor _).map ((cutK₀ A B Z).map f₂)
  rw [FiltQuot.functor_map_eq_iff, ← Functor.map_sub]
  obtain ⟨U, hU, a, b, hab⟩ := h
  have h1 : FiltQuot.ideal (suppIn (A ∪ B) (B ∪ Z)) (f₁ - f₂).hom :=
    ⟨U.obj, hU, a.hom, b.hom, congrArg (fun f => f.hom) hab⟩
  obtain ⟨W', hW', a', b', hab'⟩ := ideal_quotSupp_of_ideal_union _ h1
  obtain ⟨α, hα⟩ := (FiltQuot.functor (suppIn (A ∪ B) Z)).map_surjective a'
  obtain ⟨β, hβ⟩ := (FiltQuot.functor (suppIn (A ∪ B) Z)).map_surjective b'
  have h3 : (cutK₀ A B Z).map (f₁ - f₂) =
      (cutK₀ A B Z).map (ObjectProperty.homMk (α ≫ β) : x ⟶ y) := by
    refine ObjectProperty.hom_ext _ ?_
    change (FiltQuot.functor _).map (f₁ - f₂).hom = (FiltQuot.functor _).map (α ≫ β)
    rw [Functor.map_comp, hα, hβ, hab']
  rw [h3]
  obtain ⟨U'', hU'', a'', b'', hab''⟩ := ideal_inter_of_excision (S := A ∪ B) subset_rfl hB
    (ObjectProperty.homMk (α ≫ β) : x ⟶ y) ⟨W'.as, hW', α, β, rfl⟩
  exact ⟨(cutK₀ A B Z).obj U'', hU'', (cutK₀ A B Z).map a'', (cutK₀ A B Z).map b'',
    by rw [hab'', Functor.map_comp]⟩

end Functors

section Pair

variable [IsIsometricVAdd (ZMod p) X] {A B Z : Set X}

variable (A B Z) in
/-- `K : 𝒰'_A/(𝒰'_A ∩ 𝒰'_{B ∪ Z}) → 𝒰_A/(𝒰_A ∩ 𝒰_B)`, the identity on objects and on
representatives. -/
private abbrev cutK (hB : ∀ c : ZMod p, ∀ x ∈ B, c +ᵥ x ∈ B) :
    FiltQuot (ExcisivePair.inter (suppIn (G := G) (A ∪ B) A) (suppIn (A ∪ B) (B ∪ Z))) ⥤
      FiltQuot (ExcisivePair.inter (quotSupp (G := G) (A ∪ B) Z A) (quotSupp (A ∪ B) Z B)) :=
  CategoryTheory.Quotient.lift _ (cutK₀ A B Z ⋙ FiltQuot.functor _) (cutK₀_compat hB)

private theorem cutK_map (hB : ∀ c : ZMod p, ∀ x ∈ B, c +ᵥ x ∈ B)
    {x y : (suppIn (G := G) (A ∪ B) A).FullSubcategory} (f : x ⟶ y) :
    (cutK A B Z hB).map ((FiltQuot.functor _).map f) =
      (FiltQuot.functor _).map ((cutK₀ A B Z).map f) :=
  CategoryTheory.Quotient.lift_map_functor_map _ _ _ _

private instance (hB : ∀ c : ZMod p, ∀ x ∈ B, c +ᵥ x ∈ B) : (cutK (G := G) A B Z hB).Additive where
  map_add {_ _ f g} := by
    obtain ⟨f, rfl⟩ := (FiltQuot.functor _).map_surjective f
    obtain ⟨g, rfl⟩ := (FiltQuot.functor _).map_surjective g
    rw [← Functor.map_add, cutK_map, cutK_map, cutK_map, Functor.map_add, Functor.map_add]

private instance (hB : ∀ c : ZMod p, ∀ x ∈ B, c +ᵥ x ∈ B) :
    (cutK (G := G) A B Z hB).Linear ℚ where
  map_smul {_ _} f c := by
    obtain ⟨f, rfl⟩ := (FiltQuot.functor _).map_surjective f
    rw [← Functor.map_smul, cutK_map, cutK_map, Functor.map_smul, Functor.map_smul]

private theorem cutK_map_dualHom (hB : ∀ c : ZMod p, ∀ x ∈ B, c +ᵥ x ∈ B)
    {M N : FiltQuot (ExcisivePair.inter (suppIn (G := G) (A ∪ B) A) (suppIn (A ∪ B) (B ∪ Z)))}
    (f : M ⟶ N) : (cutK A B Z hB).map (dualHom f) = dualHom ((cutK A B Z hB).map f) := by
  obtain ⟨g, rfl⟩ := (FiltQuot.functor _).map_surjective f
  rw [FiltQuot.dualHom_map, cutK_map, cutK_map, FiltQuot.dualHom_map]
  rfl

variable (A B Z) in
/-- `K` as a strict duality functor. -/
private def cutKDual (hB : ∀ c : ZMod p, ∀ x ∈ B, c +ᵥ x ∈ B) :
    DualFunctor
      (FiltQuot (ExcisivePair.inter (suppIn (G := G) (A ∪ B) A) (suppIn (A ∪ B) (B ∪ Z))))
      (FiltQuot (ExcisivePair.inter (quotSupp (G := G) (A ∪ B) Z A) (quotSupp (A ∪ B) Z B))) where
  toFunctor := cutK A B Z hB
  ξ _ := Iso.refl _
  ξ_natural f :=
    (Category.comp_id _).trans ((cutK_map_dualHom hB f).trans (Category.id_comp _).symm)
  ξ_dual _ := (dualHom_id _).trans ((eqToHom_refl _ _).symm.trans (Category.comp_id _).symm)

omit [MetricSpace X] [IsIsometricVAdd (ZMod p) X] in
private theorem union_invariant (hB : ∀ c : ZMod p, ∀ x ∈ B, c +ᵥ x ∈ B)
    (hZ : ∀ c : ZMod p, ∀ x ∈ Z, c +ᵥ x ∈ Z) : ∀ c : ZMod p, ∀ x ∈ B ∪ Z, c +ᵥ x ∈ B ∪ Z :=
  fun c x hx => hx.elim (fun h => Or.inl (hB c x h)) (fun h => Or.inr (hZ c x h))

omit [MetricSpace X] [IsIsometricVAdd (ZMod p) X] in
private theorem union_subset_union : A ∪ B ⊆ A ∪ (B ∪ Z) :=
  Set.union_subset_union_right A Set.subset_union_left

variable (A B Z) in
/-- The excision equivalence for `A` and `B ∪ Z` inside `𝒜_S`. -/
private noncomputable abbrev cutExc (hB : ∀ c : ZMod p, ∀ x ∈ B, c +ᵥ x ∈ B)
    (hZ : ∀ c : ZMod p, ∀ x ∈ Z, c +ᵥ x ∈ Z) :=
  excision (G := G) (A ∪ B) A (B ∪ Z) union_subset_union (union_invariant hB hZ)

variable (A B Z) in
/-- `F = K ∘ r₀ ∘ q : 𝒜_S → 𝒰_A/(𝒰_A ∩ 𝒰_B)`, with `q : 𝒜_S → 𝒜_S/𝒜_{B ∪ Z}`. -/
private noncomputable abbrev cutF (hB : ∀ c : ZMod p, ∀ x ∈ B, c +ᵥ x ∈ B)
    (hZ : ∀ c : ZMod p, ∀ x ∈ Z, c +ᵥ x ∈ Z) :
    DualFunctor (supp (A ∪ B) : ObjectProperty (AsymCat G X)).FullSubcategory
      (FiltQuot (ExcisivePair.inter (quotSupp (G := G) (A ∪ B) Z A) (quotSupp (A ∪ B) Z B))) :=
  (FiltQuot.q (suppIn (A ∪ B) (B ∪ Z))).comp ((cutExc A B Z hB hZ).1.comp (cutKDual A B Z hB))

private theorem cutF_compat (hB : ∀ c : ZMod p, ∀ x ∈ B, c +ᵥ x ∈ B)
    (hZ : ∀ c : ZMod p, ∀ x ∈ Z, c +ᵥ x ∈ Z)
    (x y : (supp (A ∪ B) : ObjectProperty (AsymCat G X)).FullSubcategory) (f₁ f₂ : x ⟶ y)
    (h : FiltQuot.rel (suppIn (A ∪ B) Z) f₁ f₂) :
    (cutF (G := G) A B Z hB hZ).toFunctor.map f₁ = (cutF A B Z hB hZ).toFunctor.map f₂ := by
  change ((cutExc A B Z hB hZ).1.comp (cutKDual A B Z hB)).toFunctor.map
      ((FiltQuot.functor _).map f₁) =
    ((cutExc A B Z hB hZ).1.comp (cutKDual A B Z hB)).toFunctor.map ((FiltQuot.functor _).map f₂)
  congr 1
  rw [FiltQuot.functor_map_eq_iff]
  obtain ⟨V, hV, a, b, hab⟩ := h
  exact ⟨V, fun ε hε => (hV ε hε).mono fun _ hi k =>
    thickening_subset_of_subset ε Set.subset_union_right (hi k), a, b, hab⟩

variable (A B Z) in
/-- The lift of `F` to `𝒬 = 𝒜_S/𝒜_Z`. -/
private noncomputable abbrev cutF₁ (hB : ∀ c : ZMod p, ∀ x ∈ B, c +ᵥ x ∈ B)
    (hZ : ∀ c : ZMod p, ∀ x ∈ Z, c +ᵥ x ∈ Z) :
    DualFunctor (FiltQuot (suppIn (G := G) (A ∪ B) Z))
      (FiltQuot (ExcisivePair.inter (quotSupp (G := G) (A ∪ B) Z A) (quotSupp (A ∪ B) Z B))) :=
  FiltQuot.liftDual _ (cutF A B Z hB hZ) (cutF_compat hB hZ)

omit [IsIsometricVAdd (ZMod p) X] in
/-- On representatives, `I [[u]] = [u]`. -/
private theorem cutI_rep
    {M N : (supp (A ∪ B) : ObjectProperty (AsymCat G X)).FullSubcategory} (f : M ⟶ N) :
    (iteratedQuotient (G := G) (A ∪ B) B Z).1.1.toFunctor.map
        ((FiltQuot.functor (quotSupp (A ∪ B) Z B)).map ((FiltQuot.functor _).map f)) =
      (FiltQuot.functor (suppIn (A ∪ B) (B ∪ Z))).map f := by
  have h := CategoryTheory.Functor.congr_hom
    (iteratedQuotient (G := G) (A ∪ B) B Z).2.2.2.2.2.1 f
  erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id] at h
  exact h

private theorem cutF₁_map (hB : ∀ c : ZMod p, ∀ x ∈ B, c +ᵥ x ∈ B)
    (hZ : ∀ c : ZMod p, ∀ x ∈ Z, c +ᵥ x ∈ Z)
    {x y : (supp (A ∪ B) : ObjectProperty (AsymCat G X)).FullSubcategory}
    (f : (FiltQuot.functor (suppIn (G := G) (A ∪ B) Z)).obj x ⟶ (FiltQuot.functor _).obj y) :
    (cutF₁ A B Z hB hZ).toFunctor.map f =
      ((cutExc A B Z hB hZ).1.comp (cutKDual A B Z hB)).toFunctor.map
        ((iteratedQuotient (G := G) (A ∪ B) B Z).1.1.toFunctor.map
          ((FiltQuot.functor (quotSupp (A ∪ B) Z B)).map f)) := by
  obtain ⟨u, rfl⟩ := (FiltQuot.functor _).map_surjective f
  rw [cutI_rep]
  rfl

private theorem cutF₁_compat (hB : ∀ c : ZMod p, ∀ x ∈ B, c +ᵥ x ∈ B)
    (hZ : ∀ c : ZMod p, ∀ x ∈ Z, c +ᵥ x ∈ Z)
    (x y : FiltQuot (suppIn (G := G) (A ∪ B) Z)) (f₁ f₂ : x ⟶ y)
    (h : FiltQuot.rel (quotSupp (A ∪ B) Z B) f₁ f₂) :
    (cutF₁ A B Z hB hZ).toFunctor.map f₁ = (cutF₁ A B Z hB hZ).toFunctor.map f₂ := by
  rcases x with ⟨x⟩
  rcases y with ⟨y⟩
  rw [cutF₁_map, cutF₁_map, (FiltQuot.functor_map_eq_iff _ _ _).2 h]

variable (A B Z) in
/-- `r : 𝒬/𝒰_B → 𝒰_A/(𝒰_A ∩ 𝒰_B)`, `⟨⟨M⟩⟩ ↦ K(r₀⟨M⟩)`, `[[u]] ↦ K(r₀[u])`. -/
private noncomputable def cutR (hB : ∀ c : ZMod p, ∀ x ∈ B, c +ᵥ x ∈ B)
    (hZ : ∀ c : ZMod p, ∀ x ∈ Z, c +ᵥ x ∈ Z) :
    DualFunctor (FiltQuot (quotSupp (G := G) (A ∪ B) Z B))
      (FiltQuot (ExcisivePair.inter (quotSupp (G := G) (A ∪ B) Z A) (quotSupp (A ∪ B) Z B))) :=
  FiltQuot.liftDual _ (cutF₁ A B Z hB hZ) (cutF₁_compat hB hZ)

end Pair

section UnitCounit

variable [IsIsometricVAdd (ZMod p) X] {A B Z : Set X}

/-- The duality isomorphism of `r` is the image under `K` of that of `r₀`. -/
private theorem cutR_ξ (hB : ∀ c : ZMod p, ∀ x ∈ B, c +ᵥ x ∈ B)
    (hZ : ∀ c : ZMod p, ∀ x ∈ Z, c +ᵥ x ∈ Z)
    (N : (supp (A ∪ B) : ObjectProperty (AsymCat G X)).FullSubcategory) :
    ((cutR A B Z hB hZ).ξ ⟨⟨N⟩⟩).hom = (cutK A B Z hB).map ((cutExc A B Z hB hZ).1.ξ ⟨N⟩).hom := by
  change ((cutF A B Z hB hZ).ξ N).hom = _
  rw [DualFunctor.comp_ξ, Iso.trans_hom, Functor.mapIso_hom, DualFunctor.comp_ξ,
    Iso.trans_hom, Functor.mapIso_hom]
  have hq : ((FiltQuot.q (suppIn (G := G) (A ∪ B) (B ∪ Z))).ξ N).hom = 𝟙 _ := rfl
  rw [hq]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact Category.comp_id _

variable (A B Z) in
/-- The unit `id ≅ r ∘ e`, the image under `K` of the unit of the excision equivalence. -/
private noncomputable def cutUnit (hB : ∀ c : ZMod p, ∀ x ∈ B, c +ᵥ x ∈ B)
    (hZ : ∀ c : ZMod p, ∀ x ∈ Z, c +ᵥ x ∈ Z) :
    DualFunctor.UnitaryIso (DualFunctor.id _)
      ((ExcisivePair.e (quotSupp (G := G) (A ∪ B) Z A) (quotSupp (A ∪ B) Z B)).comp
        (cutR A B Z hB hZ)) where
  iso := NatIso.ofComponents (fun M => (cutK A B Z hB).mapIso
      ((cutExc A B Z hB hZ).2.1.iso.app ⟨⟨M.as.obj.as, M.as.property⟩⟩)) (by
    rintro ⟨⟨⟨M⟩, hM⟩⟩ ⟨⟨⟨N⟩, hN⟩⟩ g
    obtain ⟨g₁, rfl⟩ := (FiltQuot.functor _).map_surjective g
    obtain ⟨f, hf⟩ := (FiltQuot.functor (suppIn (A ∪ B) Z)).map_surjective g₁.hom
    let f' : (⟨M, hM⟩ : (suppIn (G := G) (A ∪ B) A).FullSubcategory) ⟶ ⟨N, hN⟩ :=
      ObjectProperty.homMk f
    have hg : (FiltQuot.functor _).map g₁ =
        (cutK A B Z hB).map ((FiltQuot.functor _).map f') := by
      rw [cutK_map]
      exact congrArg _ (ObjectProperty.hom_ext _ hf.symm)
    have hn := congrArg (cutK A B Z hB).map
      ((cutExc A B Z hB hZ).2.1.iso.hom.naturality ((FiltQuot.functor _).map f'))
    rw [Functor.map_comp, Functor.map_comp] at hn
    rw [hg]
    refine hn.trans ?_
    congr 1)
  unitary M := by
    rcases M with ⟨⟨⟨M⟩, hM⟩⟩
    have hu := (cutExc A B Z hB hZ).2.1.unitary ⟨⟨M, hM⟩⟩
    have h₀ : ((ExcisivePair.e (suppIn (G := G) (A ∪ B) A) (suppIn (A ∪ B) (B ∪ Z))).ξ
        ⟨⟨M, hM⟩⟩).hom = 𝟙 _ := rfl
    simp only [DualFunctor.comp_ξ, Iso.trans_hom, Functor.mapIso_hom, DualFunctor.id_ξ,
      Iso.refl_hom, h₀, CategoryTheory.Functor.map_id] at hu
    have h := congrArg (cutK A B Z hB).map hu
    simp only [Functor.map_comp] at h
    have h₁ : ((ExcisivePair.e (quotSupp (G := G) (A ∪ B) Z A) (quotSupp (A ∪ B) Z B)).ξ
        ⟨⟨⟨M⟩, hM⟩⟩).hom = 𝟙 _ := rfl
    simp only [DualFunctor.comp_ξ, Iso.trans_hom, Functor.mapIso_hom, DualFunctor.id_ξ,
      Iso.refl_hom, h₁, CategoryTheory.Functor.map_id]
    refine (congrArg (fun t => _ ≫ (𝟙 _ ≫ t) ≫ _) (cutR_ξ hB hZ M)).trans ?_
    exact h

omit [IsIsometricVAdd (ZMod p) X] in
private theorem cutP_compat (x y : (supp (A ∪ B) : ObjectProperty (AsymCat G X)).FullSubcategory)
    (f₁ f₂ : x ⟶ y) (h : FiltQuot.rel (suppIn (A ∪ B) (B ∪ Z)) f₁ f₂) :
    ((FiltQuot.q (suppIn (G := G) (A ∪ B) Z)).comp
        (FiltQuot.q (quotSupp (A ∪ B) Z B))).toFunctor.map f₁ =
      ((FiltQuot.q (suppIn (G := G) (A ∪ B) Z)).comp
        (FiltQuot.q (quotSupp (A ∪ B) Z B))).toFunctor.map f₂ := by
  change (FiltQuot.functor _).map ((FiltQuot.functor _).map f₁) =
    (FiltQuot.functor _).map ((FiltQuot.functor _).map f₂)
  rw [FiltQuot.functor_map_eq_iff, ← Functor.map_sub]
  exact ideal_quotSupp_of_ideal_union _ h

variable (A B Z) in
/-- `P : 𝒜_S/𝒜_{B ∪ Z} → 𝒬/𝒰_B`, `[u] ↦ [[u]]` (the inverse of the iterated quotient). -/
private noncomputable abbrev cutP :
    DualFunctor (FiltQuot (suppIn (G := G) (A ∪ B) (B ∪ Z)))
      (FiltQuot (quotSupp (G := G) (A ∪ B) Z B)) :=
  FiltQuot.liftDual _ ((FiltQuot.q (suppIn (A ∪ B) Z)).comp (FiltQuot.q (quotSupp (A ∪ B) Z B)))
    cutP_compat

private theorem cut_starP (hB : ∀ c : ZMod p, ∀ x ∈ B, c +ᵥ x ∈ B)
    {M N : FiltQuot (ExcisivePair.inter (suppIn (G := G) (A ∪ B) A) (suppIn (A ∪ B) (B ∪ Z)))}
    (f : M ⟶ N) :
    (ExcisivePair.e (quotSupp (G := G) (A ∪ B) Z A) (quotSupp (A ∪ B) Z B)).toFunctor.map
        ((cutK A B Z hB).map f) =
      (cutP A B Z).toFunctor.map
        ((ExcisivePair.e (suppIn (G := G) (A ∪ B) A) (suppIn (A ∪ B) (B ∪ Z))).toFunctor.map f) := by
  obtain ⟨g, rfl⟩ := (FiltQuot.functor _).map_surjective f
  rfl

variable (A B Z) in
/-- The counit `e ∘ r ≅ id`, the image under `I⁻¹` of the counit of the excision equivalence. -/
private noncomputable def cutCounit (hB : ∀ c : ZMod p, ∀ x ∈ B, c +ᵥ x ∈ B)
    (hZ : ∀ c : ZMod p, ∀ x ∈ Z, c +ᵥ x ∈ Z) :
    DualFunctor.UnitaryIso ((cutR A B Z hB hZ).comp
      (ExcisivePair.e (quotSupp (G := G) (A ∪ B) Z A) (quotSupp (A ∪ B) Z B)))
      (DualFunctor.id _) where
  iso := NatIso.ofComponents (fun M => (cutP A B Z).toFunctor.mapIso (Y := ⟨M.as.as⟩)
      ((cutExc A B Z hB hZ).2.2.iso.app ⟨M.as.as⟩)) (by
    rintro ⟨⟨M⟩⟩ ⟨⟨N⟩⟩ g
    obtain ⟨g', rfl⟩ := (FiltQuot.functor _).map_surjective g
    obtain ⟨f, rfl⟩ := (FiltQuot.functor _).map_surjective g'
    have hn := congrArg (cutP A B Z).toFunctor.map
      ((cutExc A B Z hB hZ).2.2.iso.hom.naturality
        ((FiltQuot.functor (suppIn (A ∪ B) (B ∪ Z))).map f :
          (⟨M⟩ : FiltQuot (suppIn (G := G) (A ∪ B) (B ∪ Z))) ⟶ ⟨N⟩))
    rw [Functor.map_comp, Functor.map_comp] at hn
    have h1 : ((cutR A B Z hB hZ).comp
        (ExcisivePair.e (quotSupp (G := G) (A ∪ B) Z A) (quotSupp (A ∪ B) Z B))).toFunctor.map
          ((FiltQuot.functor _).map ((FiltQuot.functor _).map f)) =
        (cutP A B Z).toFunctor.map
          ((ExcisivePair.e (suppIn (G := G) (A ∪ B) A) (suppIn (A ∪ B) (B ∪ Z))).toFunctor.map
            ((cutExc A B Z hB hZ).1.toFunctor.map
              ((FiltQuot.functor (suppIn (A ∪ B) (B ∪ Z))).map f :
                (⟨M⟩ : FiltQuot (suppIn (G := G) (A ∪ B) (B ∪ Z))) ⟶ ⟨N⟩))) :=
      cut_starP (A := A) (Z := Z) hB
        ((cutExc A B Z hB hZ).1.toFunctor.map ((FiltQuot.functor (suppIn (A ∪ B) (B ∪ Z))).map f :
          (⟨M⟩ : FiltQuot (suppIn (G := G) (A ∪ B) (B ∪ Z))) ⟶ ⟨N⟩))
    rw [h1]
    exact hn)
  unitary M := by
    rcases M with ⟨⟨M⟩⟩
    have hc := (cutExc A B Z hB hZ).2.2.unitary ⟨M⟩
    have h₀ : ∀ N, ((ExcisivePair.e (suppIn (G := G) (A ∪ B) A) (suppIn (A ∪ B) (B ∪ Z))).ξ
        N).hom = 𝟙 _ := fun _ => rfl
    simp only [DualFunctor.comp_ξ, Iso.trans_hom, Functor.mapIso_hom, DualFunctor.id_ξ,
      Iso.refl_hom, h₀, Category.comp_id] at hc
    have h := congrArg (cutP A B Z).toFunctor.map hc
    simp only [Functor.map_comp] at h
    have h₁ : ∀ N, ((ExcisivePair.e (quotSupp (G := G) (A ∪ B) Z A) (quotSupp (A ∪ B) Z B)).ξ
        N).hom = 𝟙 _ := fun _ => rfl
    simp only [DualFunctor.comp_ξ, Iso.trans_hom, Functor.mapIso_hom, DualFunctor.id_ξ,
      Iso.refl_hom, h₁, Category.comp_id]
    refine h.trans ((congrArg (ExcisivePair.e (quotSupp (G := G) (A ∪ B) Z A)
      (quotSupp (A ∪ B) Z B)).toFunctor.map (cutR_ξ hB hZ M)).trans (cut_starP hB _)).symm
end UnitCounit

/-- **Cut square.** -/
noncomputable def cutSquare [IsIsometricVAdd (ZMod p) X] [CompactSpace X] {A B Z : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (hAi : ∀ c : ZMod p, ∀ x ∈ A, c +ᵥ x ∈ A) (hBi : ∀ c : ZMod p, ∀ x ∈ B, c +ᵥ x ∈ B)
    (hZi : ∀ c : ZMod p, ∀ x ∈ Z, c +ᵥ x ∈ Z) :
    {E : ExcisivePair (FiltQuot (suppIn (G := G) (A ∪ B) Z)) //
      E.UA = quotSupp (A ∪ B) Z A ∧ E.UB = quotSupp (A ∪ B) Z B ∧
        ∀ V : E.UA.FullSubcategory,
          ExcisivePair.inter E.UA E.UB V ↔ quotSupp (A ∪ B) Z (A ∩ B) V.obj} :=
  ⟨{ UA := quotSupp (A ∪ B) Z A
     UB := quotSupp (A ∪ B) Z B
     filtA := quotSupp_karoubiFiltration (A ∪ B) Z hAi
     filtB := quotSupp_karoubiFiltration (A ∪ B) Z hBi
     filtY := cutFiltY Z hBi
     r := cutR A B Z hBi hZi
     unit := cutUnit A B Z hBi hZi
     counit := cutCounit A B Z hBi hZi }, rfl, rfl, fun V =>
    ⟨fun h => (supp_inter hA hB _).1 ⟨V.property, h⟩, fun h => ((supp_inter hA hB _).2 h).2⟩⟩

section NonVacuity

/-- The trivial action of `C_2` on a point (for the non-vacuity witness). -/
private abbrev unitAction : AddAction (ZMod 2) Unit where
  vadd _ x := x
  zero_vadd _ := rfl
  add_vadd _ _ _ := rfl

attribute [local instance] unitAction

/-- Non-vacuity: the cut square for `X` a point with the trivial (isometric) action of `C_2`, the
trivial group sequence, `A = B = X` and `Z = ∅`, an excisive pair in `𝒜_X/𝒜_∅`. -/
private noncomputable def cutSquare_unit :
    ExcisivePair (FiltQuot (suppIn (G := GroupSeq.trivial 2)
      ((Set.univ : Set Unit) ∪ Set.univ) ∅)) :=
  letI : IsIsometricVAdd (ZMod 2) Unit := ⟨fun _ => isometry_subsingleton⟩
  (cutSquare (G := GroupSeq.trivial 2) (A := (Set.univ : Set Unit)) (B := Set.univ)
    (Z := (∅ : Set Unit)) isClosed_univ isClosed_univ (fun _ _ _ => Set.mem_univ _)
    (fun _ _ _ => Set.mem_univ _) (fun _ _ h => h)).1

end NonVacuity

end HSP
