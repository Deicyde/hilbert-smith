import HilbertSmithPaper.LTheory.Base.Categories.UnitaryIsomorphism

/-!
# Identity and composite of unitary isomorphisms

The identity natural isomorphism of a duality functor `(F, ξ)` is unitary, and if
`η : F ≅ G` and `θ : G ≅ H` are unitary then so is `θ ∘ η : F ≅ H`.

## Encoding

A unitary natural isomorphism is data (the structure `DualFunctor.UnitaryIso`), so the two facts
are the constructions `DualFunctor.UnitaryIso.refl` (the identity natural isomorphism with its
unitarity) and `DualFunctor.UnitaryIso.trans` (the composite `η ≪≫ θ` with its unitarity); both
belong to the article.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v₁ v₂ u₁ u₂

variable {A : Type u₁} [Category.{v₁} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]
  {B : Type u₂} [Category.{v₂} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

/-- The identity natural isomorphism of a duality functor is unitary. -/
def DualFunctor.UnitaryIso.refl (F : DualFunctor A B) : DualFunctor.UnitaryIso F F where
  iso := Iso.refl _
  unitary M := by simp

/-- A composite of unitary natural isomorphisms is unitary. -/
def DualFunctor.UnitaryIso.trans {F G H : DualFunctor A B} (η : DualFunctor.UnitaryIso F G)
    (θ : DualFunctor.UnitaryIso G H) : DualFunctor.UnitaryIso F H where
  iso := η.iso ≪≫ θ.iso
  unitary M := by
    rw [Iso.trans_hom, NatTrans.comp_app, NatTrans.comp_app, dualHom_comp, ← η.unitary M,
      ← θ.unitary M]
    simp only [Category.assoc]

end HSP
