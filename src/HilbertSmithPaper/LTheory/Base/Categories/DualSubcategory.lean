import HilbertSmithPaper.LTheory.Base.Categories.DualAdditiveSubcategory
import HilbertSmithPaper.LTheory.Base.Categories.DualityFunctor

/-!
# Duality category of a dual-closed additive subcategory

For a full additive subcategory `𝒰 ⊂ 𝒜` closed under duality (`HSP.IsDualAdditive U`), the full
subcategory `U.FullSubcategory` (objects of `𝒜` satisfying `U`, all morphisms of `𝒜`) is a
duality category: it is preadditive and ℚ-linear (Mathlib), it has finite biproducts (a zero
object of `𝒰`, and for `V, W` in `𝒰` a biproduct bicone with cone point in `𝒰`, which stays a
biproduct in the full subcategory), and the duality of `𝒜` restricts to it. The inclusion
`𝒰 → 𝒜` is a strict duality functor (`DualSubcategory.incl`).
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A] (U : ObjectProperty A) [IsDualAdditive U]

namespace DualSubcategory

omit [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A] [DualCat A] [IsDualAdditive U] in
private lemma isZero_of_mem {Z : A} (hZ : U Z) (h : IsZero Z) : IsZero (⟨Z, hZ⟩ : U.FullSubcategory) :=
  ⟨fun Y => ⟨⟨⟨ObjectProperty.homMk (h.to_ Y.obj)⟩, fun _ =>
      ObjectProperty.hom_ext _ (h.eq_of_src _ _)⟩⟩,
    fun Y => ⟨⟨⟨ObjectProperty.homMk (h.from_ Y.obj)⟩, fun _ =>
      ObjectProperty.hom_ext _ (h.eq_of_tgt _ _)⟩⟩⟩

private lemma hasBinaryBiproduct (V W : U.FullSubcategory) : HasBinaryBiproduct V W := by
  obtain ⟨c, ⟨hc⟩, hpt⟩ := IsDualAdditive.exists_biprod V.property W.property
  let b : BinaryBicone V W :=
    { pt := ⟨c.pt, hpt⟩
      fst := ObjectProperty.homMk c.fst
      snd := ObjectProperty.homMk c.snd
      inl := ObjectProperty.homMk c.inl
      inr := ObjectProperty.homMk c.inr
      inl_fst := ObjectProperty.hom_ext _ c.inl_fst
      inl_snd := ObjectProperty.hom_ext _ c.inl_snd
      inr_fst := ObjectProperty.hom_ext _ c.inr_fst
      inr_snd := ObjectProperty.hom_ext _ c.inr_snd }
  exact HasBinaryBiproduct.mk ⟨b, isBinaryBilimitOfTotal b
    (ObjectProperty.hom_ext _ (IsBilimit.binary_total hc))⟩

instance : HasBinaryBiproducts U.FullSubcategory := ⟨hasBinaryBiproduct U⟩

instance : HasZeroObject U.FullSubcategory := by
  obtain ⟨Z, hZ, h⟩ := IsDualAdditive.exists_zero (U := U)
  exact ⟨⟨⟨Z, hZ⟩, isZero_of_mem U hZ h⟩⟩

instance : HasFiniteBiproducts U.FullSubcategory := by
  have : HasFiniteProducts U.FullSubcategory := hasFiniteProducts_of_has_binary_and_terminal
  exact HasFiniteBiproducts.of_hasFiniteProducts

end DualSubcategory

/-- The duality of `𝒜` restricted to a dual-closed additive subcategory `𝒰`: `𝒰` is a duality
category. -/
instance instDualCatFullSubcategory : DualCat U.FullSubcategory where
  dual V := ⟨dual V.obj, IsDualAdditive.dual_mem V.property⟩
  dualHom f := ObjectProperty.homMk (dualHom f.hom)
  dualHom_id V := ObjectProperty.hom_ext _ (dualHom_id V.obj)
  dualHom_comp f g := ObjectProperty.hom_ext _ (dualHom_comp f.hom g.hom)
  dualHom_add f g := ObjectProperty.hom_ext _ (dualHom_add f.hom g.hom)
  dualHom_smul c f := ObjectProperty.hom_ext _ (dualHom_smul c f.hom)
  dual_dual V := ObjectProperty.FullSubcategory.ext (dual_dual V.obj)
  dualHom_dualHom f := ObjectProperty.hom_ext _ (by simp [dualHom_dualHom])
  dualHom_zero := ObjectProperty.hom_ext _ dualHom_zero
  dualHom_neg f := ObjectProperty.hom_ext _ (dualHom_neg f.hom)
  dualHom_sub f g := ObjectProperty.hom_ext _ (dualHom_sub f.hom g.hom)
  dualHom_eqToHom h := by subst h; exact ObjectProperty.hom_ext _ (by simp)

namespace DualSubcategory

instance : U.ι.Linear ℚ where
  map_smul _ _ := rfl

private lemma ι_dual (V : U.FullSubcategory) : U.ι.obj (dual V) = dual (U.ι.obj V) := rfl

/-- The inclusion `𝒰 → 𝒜` as a strict duality functor (`ξ` the identity). -/
def incl : DualFunctor U.FullSubcategory A where
  toFunctor := U.ι
  ξ V := Iso.refl _
  ξ_natural f := by simp; rfl
  ξ_dual V := by simp; rfl

/-- The inclusion is a strict duality functor. -/
theorem incl_isStrict : (incl U).IsStrict := fun _ => ⟨rfl, rfl⟩

end DualSubcategory

end HSP
