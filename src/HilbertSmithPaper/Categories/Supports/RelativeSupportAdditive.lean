import HilbertSmithPaper.Categories.Supports.RelativeSupport
import HilbertSmithPaper.Categories.Supports.SupportConcatenation

/-!
# The support subcategory inside a support subcategory is additive

`𝒜_{S'} ⊂ 𝒜_S` is a full additive subcategory closed under duality (`HSP.isDualAdditive_suppIn`):
it contains the empty sequence (a zero object of `𝒜_S`), the concatenation of two of its objects
(a biproduct in `𝒜_S`), and `M^* = M`. So the quotient `𝒜_S/𝒜_{S'}` is defined.
-/

open CategoryTheory CategoryTheory.Limits Filter

namespace HSP

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

/-- The empty sequence is `S`-supported. -/
private theorem supp_zero (S : Set X) : supp S (⟨AsymPre.zero⟩ : AsymCat G X) :=
  fun _ _ => Eventually.of_forall fun _ k => k.elim0

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


end HSP
