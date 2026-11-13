import HilbertSmithPaper.Categories.Cuts.CutSquare
import HilbertSmithPaper.LTheory.Base.Categories.DualityFunctors.StrictDualityFunctor
import HilbertSmithPaper.LTheory.Base.Categories.DualityFunctors.CompositeDualityFunctor
import HilbertSmithPaper.Categories.Supports.QuotientSeparationIso
import HilbertSmithPaper.LTheory.Ultimate.Boundary.ExcisionBoundary

/-!
# Cut boundary

Let `X` be compact with an isometric `C_p`-action, `A, B, Z ⊆ X` closed and invariant with
`Z ∩ B = ∅`, `S = A ∪ B` and `Y = A ∩ B`. The cut boundary (`HSP.cutBoundary`)
`∂_{A,B} : 𝕃_k(𝒜_S/𝒜_Z) → 𝕃_{k-1}(𝒜_Y)` is the excision boundary of the cut square, landing in
`𝕃_{k-1}(𝒰_A ∩ 𝒰_B)`, followed by the map induced by `σ ∘ β`. Here `β : 𝒰_A ∩ 𝒰_B → 𝒰_Y` is the
identity on objects and morphisms (`𝒰_A ∩ 𝒰_B = 𝒰_Y` by support intersection), and
`σ : 𝒰_Y → 𝒜_Y` is the inverse in separated support.
-/

open CategoryTheory

namespace HSP

open DualCat

/-! `β` is set up for arbitrary predicates `U_A, U_B, U_Y` on a category and then specialised;
stated for the concrete support predicates, the kernel spends minutes comparing `supp A` with
`supp (A ∩ B)` while checking it. -/

section BetaGeneric

variable {C : Type*} [Category C] [Preadditive C] [Linear ℚ C] [Limits.HasFiniteBiproducts C]
  [DualCat C]
  {UA UB UY : ObjectProperty C} [IsDualAdditive UA] [IsDualAdditive (ExcisivePair.inter UA UB)]
  [IsDualAdditive UY]

/-- `β : U_A ∩ U_B → U_Y`, the identity on objects and morphisms. -/
private abbrev gBeta (h : ∀ V : (ExcisivePair.inter UA UB).FullSubcategory, UY V.obj.obj) :
    (ExcisivePair.inter UA UB).FullSubcategory ⥤ UY.FullSubcategory :=
  ObjectProperty.lift _ ((ExcisivePair.inter _ _).ι ⋙ UA.ι) h

private instance (h : ∀ V : (ExcisivePair.inter UA UB).FullSubcategory, UY V.obj.obj) :
    (gBeta h).Additive where
  map_add := ObjectProperty.hom_ext _ rfl

private instance (h : ∀ V : (ExcisivePair.inter UA UB).FullSubcategory, UY V.obj.obj) :
    (gBeta h).Linear ℚ where
  map_smul _ _ := ObjectProperty.hom_ext _ rfl

/-- `β` as a strict duality functor. -/
private def gBetaDual (h : ∀ V : (ExcisivePair.inter UA UB).FullSubcategory, UY V.obj.obj) :
    DualFunctor (ExcisivePair.inter UA UB).FullSubcategory UY.FullSubcategory where
  toFunctor := gBeta h
  ξ _ := Iso.refl _
  ξ_natural f := (Category.comp_id _).trans
    ((ObjectProperty.hom_ext _ rfl : (gBeta h).map (dualHom f) =
      dualHom ((gBeta h).map f)).trans (Category.id_comp _).symm)
  ξ_dual _ := (dualHom_id _).trans ((eqToHom_refl _ _).symm.trans (Category.comp_id _).symm)

end BetaGeneric

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]
  [CompactSpace X] {A B Z : Set X}

variable (Z) in
/-- `β : 𝒰_A ∩ 𝒰_B → 𝒰_Y` as a strict duality functor, the identity on objects and morphisms. -/
private def cutBetaDual (hA : IsClosed A) (hB : IsClosed B) :
    DualFunctor
      (ExcisivePair.inter (quotSupp (G := G) (A ∪ B) Z A) (quotSupp (A ∪ B) Z B)).FullSubcategory
      (quotSupp (G := G) (A ∪ B) Z (A ∩ B)).FullSubcategory :=
  gBetaDual fun V => (supp_inter hA hB _).1 ⟨V.obj.property, V.property⟩

variable [IsIsometricVAdd (ZMod p) X]

/-- **Cut boundary.** `∂_{A,B} : 𝕃_k(𝒜_S/𝒜_Z) → 𝕃_{k-1}(𝒜_Y)`, `S = A ∪ B`, `Y = A ∩ B`: the
excision boundary of the cut square followed by the map induced by `σ ∘ β`, where `β` identifies
`𝒰_A ∩ 𝒰_B` with `𝒰_Y` and `σ : 𝒰_Y → 𝒜_Y` is the inverse in separated support. -/
noncomputable def cutBoundary {S Y : Set X} (hS : S = A ∪ B) (hY : Y = A ∩ B)
    (hA : IsClosed A) (hB : IsClosed B) (hZ : IsClosed Z)
    (hAi : ∀ c : ZMod p, ∀ x ∈ A, c +ᵥ x ∈ A) (hBi : ∀ c : ZMod p, ∀ x ∈ B, c +ᵥ x ∈ B)
    (hZi : ∀ c : ZMod p, ∀ x ∈ Z, c +ᵥ x ∈ Z) (hZB : Disjoint Z B) (k : ℤ) :
    ultL (FiltQuot (suppIn (G := G) S Z)) k →+
      ultL (supp Y : ObjectProperty (AsymCat G X)).FullSubcategory (k - 1) := by
  subst hS hY
  exact (ultL.map ((cutBetaDual Z hA hB).comp
      (quotientSeparationIso (A ∪ B) (hA.inter hB) hZ
        (fun c x hx => ⟨hAi c x hx.1, hBi c x hx.2⟩) hZi
        (hZB.symm.mono_left Set.inter_subset_right)
        (fun _ hx => Or.inl hx.1)).1.2) (k - 1)).comp
    ((cutSquare hA hB hAi hBi hZi).1.boundary k)

end HSP
