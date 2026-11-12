import HilbertSmithPaper.LTheory.Base.Categories.DualSubcategory

/-!
# Inclusion of a dual-closed subcategory

For a full additive subcategory `𝒰 ⊂ 𝒜` closed under duality, the inclusion `𝒰 → 𝒜` is a
ℚ-linear functor commuting with the duality on the nose: a duality functor with `ξ` the
identity. Its strictness is in `LTheory.Base.Categories.DualityFunctors.InclusionStrict`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A] (U : ObjectProperty A) [IsDualAdditive U]

namespace DualSubcategory

instance : U.ι.Linear ℚ where
  map_smul _ _ := rfl

private lemma ι_dual (V : U.FullSubcategory) : U.ι.obj (dual V) = dual (U.ι.obj V) := rfl

/-- **Inclusion of a dual-closed subcategory.** The inclusion `𝒰 → 𝒜` as a strict duality
functor (`ξ` the identity). -/
def incl : DualFunctor U.FullSubcategory A where
  toFunctor := U.ι
  ξ V := Iso.refl _
  ξ_natural f := by simp; rfl
  ξ_dual V := by simp; rfl

end DualSubcategory

end HSP
