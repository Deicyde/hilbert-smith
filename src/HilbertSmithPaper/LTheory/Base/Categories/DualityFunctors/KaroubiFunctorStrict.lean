import HilbertSmithPaper.LTheory.Base.Categories.KaroubiFunctor
import HilbertSmithPaper.LTheory.Base.Categories.DualityFunctors.StrictDualityFunctor

/-!
# The completion of a strict duality functor is strict

If `(F, ξ) : A → B` is strict, so is its completion `Kar F : Kar A → Kar B`.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

namespace HSP

open DualCat

universe v₁ v₂ u₁ u₂

variable {A : Type u₁} [Category.{v₁} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]
  {B : Type u₂} [Category.{v₂} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

namespace DualFunctor

variable (F : DualFunctor A B)

/-- The completion of a strict duality functor is strict. -/
theorem kar_isStrict (hF : F.IsStrict) : F.kar.IsStrict := by
  intro P
  obtain ⟨h, hξ⟩ := hF P.X
  have hP : F.kar.toFunctor.obj (dual P) = dual (F.kar.toFunctor.obj P) :=
    Idempotents.Karoubi.ext h (by
      change F.toFunctor.map (dualHom P.p) ≫ eqToHom h = eqToHom h ≫ dualHom (F.toFunctor.map P.p)
      rw [← hξ, F.ξ_natural])
  refine ⟨hP, Idempotents.Karoubi.hom_ext _ _ ?_⟩
  change F.toFunctor.map (dualHom P.p) ≫ (F.ξ P.X).hom = _
  rw [hξ, Idempotents.Karoubi.eqToHom_f]
  rfl

end DualFunctor

end HSP
