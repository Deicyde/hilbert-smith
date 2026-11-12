import HilbertSmithPaper.Categories.Supports.RelativeSupportAdditive
import HilbertSmithPaper.Categories.Supports.SupportConcatenation
import HilbertSmithPaper.LTheory.Ultimate.Boundary.ExcisivePair
import HilbertSmithPaper.LTheory.Ultimate.Boundary.ExcisiveIntersection

/-!
# Supported objects of a relative support subcategory are additive

For `S, A, B ⊆ X`, in the full subcategory `𝒰_A` of `A`-supported objects of `𝒜_S`
(`(suppIn S A).FullSubcategory`), the `B`-supported objects (`ExcisivePair.inter`-style predicate
`fun V => supp B V.obj.obj`, written `ExcisivePair.inter (suppIn S A) (suppIn S B)`) form a full
additive subcategory closed under duality (`HSP.isDualAdditive_exInter`): the empty sequence and
the concatenation lie in all three support subcategories, and `M^* = M`.
-/

open CategoryTheory CategoryTheory.Limits Filter

namespace HSP

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

/-- The empty sequence is `S`-supported. -/
private theorem supp_zero (S : Set X) : supp S (⟨AsymPre.zero⟩ : AsymCat G X) :=
  fun _ _ => Eventually.of_forall fun _ k => k.elim0

section Generic

variable {C : Type*} [Category C] [Preadditive C] {P : ObjectProperty C}

omit [Preadditive C] in
private theorem isZero_lift {Z : C} (hZ : P Z) (h : IsZero Z) :
    IsZero (⟨Z, hZ⟩ : P.FullSubcategory) :=
  ⟨fun Y => ⟨⟨⟨ObjectProperty.homMk (h.to_ Y.obj)⟩, fun _ =>
      ObjectProperty.hom_ext _ (h.eq_of_src _ _)⟩⟩,
    fun Y => ⟨⟨⟨ObjectProperty.homMk (h.from_ Y.obj)⟩, fun _ =>
      ObjectProperty.hom_ext _ (h.eq_of_tgt _ _)⟩⟩⟩

/-- A bicone of the underlying objects with cone point in `P`, as a bicone in the full
subcategory. -/
private def liftBicone {V W : P.FullSubcategory} (c : BinaryBicone V.obj W.obj) (h : P c.pt) :
    BinaryBicone V W where
  pt := ⟨c.pt, h⟩
  fst := ObjectProperty.homMk c.fst
  snd := ObjectProperty.homMk c.snd
  inl := ObjectProperty.homMk c.inl
  inr := ObjectProperty.homMk c.inr
  inl_fst := ObjectProperty.hom_ext _ c.inl_fst
  inl_snd := ObjectProperty.hom_ext _ c.inl_snd
  inr_fst := ObjectProperty.hom_ext _ c.inr_fst
  inr_snd := ObjectProperty.hom_ext _ c.inr_snd

private theorem liftBicone_total {V W : P.FullSubcategory} (c : BinaryBicone V.obj W.obj)
    (h : P c.pt) (ht : c.fst ≫ c.inl + c.snd ≫ c.inr = 𝟙 c.pt) :
    (liftBicone c h).fst ≫ (liftBicone c h).inl + (liftBicone c h).snd ≫ (liftBicone c h).inr =
      𝟙 (liftBicone c h).pt :=
  ObjectProperty.hom_ext _ ht

end Generic

/-- `𝒰_A ∩ 𝒰_B` is a full additive subcategory of `𝒰_A` closed under duality. -/
instance isDualAdditive_exInter (S A B : Set X) :
    IsDualAdditive (ExcisivePair.inter (suppIn (G := G) S A) (suppIn S B)) where
  exists_zero := ⟨⟨⟨⟨AsymPre.zero⟩, supp_zero S⟩, supp_zero A⟩, supp_zero B,
    isZero_lift _ (isZero_lift _ AsymCat.isZero_zero)⟩
  exists_biprod {V W} hV hW := by
    let c₀ := AsymCat.binaryBicone V.obj.obj W.obj.obj
    let c₁ := liftBicone (P := (supp S : ObjectProperty (AsymCat G X))) (V := V.obj) (W := W.obj)
      c₀ (supp_sum V.obj.property W.obj.property)
    let c₂ := liftBicone (P := suppIn S A) (V := V) (W := W) c₁ (supp_sum V.property W.property)
    exact ⟨c₂, ⟨isBinaryBilimitOfTotal _ (liftBicone_total _ _ (liftBicone_total _ _
      (AsymCat.binaryBicone_total _ _)))⟩, supp_sum hV hW⟩
  dual_mem h := h

end HSP
