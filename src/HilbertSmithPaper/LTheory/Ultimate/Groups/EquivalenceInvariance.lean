import HilbertSmithPaper.LTheory.Ultimate.Groups.InducedMap
import HilbertSmithPaper.LTheory.Base.Categories.UnitaryIsomorphism

/-!
# Equivalence invariance on ultimate L

Let `F : A → B` and `G : B → A` be duality functors with unitary natural isomorphisms
`id_A ≅ G ∘ F` and `F ∘ G ≅ id_B`. Then `F_* : 𝕃_k(A) → 𝕃_k(B)` is an isomorphism with inverse
`G_*`.

Lean: `A` and `B` have the same universe levels, as for the induced map.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]
  {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

/-- If `id_A ≅ G ∘ F` and `F ∘ G ≅ id_B` unitarily, then `G_* ∘ F_* = 1` and `F_* ∘ G_* = 1` on
the ultimate L-groups. -/
theorem ultL.map_inverse (F : DualFunctor A B) (G : DualFunctor B A)
    (η : DualFunctor.UnitaryIso (DualFunctor.id A) (F.comp G))
    (ε : DualFunctor.UnitaryIso (G.comp F) (DualFunctor.id B)) (k : ℤ) :
    (ultL.map G k).comp (ultL.map F k) = AddMonoidHom.id _ ∧
      (ultL.map F k).comp (ultL.map G k) = AddMonoidHom.id _ := by
  sorry

end HSP
