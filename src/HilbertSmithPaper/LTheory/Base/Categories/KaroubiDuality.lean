import HilbertSmithPaper.LTheory.Base.Categories.DualityCategory

/-!
# Idempotent completion with duality

For a duality category `A`, the idempotent completion `Kar A` is Mathlib's
`CategoryTheory.Idempotents.Karoubi A`: objects `(M, e)` with `e ≫ e = e`, morphisms
`f : (M, e) ⟶ (N, e')` with `e ≫ f ≫ e' = f`. Mathlib provides the preadditive structure and
finite biproducts (`karoubi_hasFiniteBiproducts`); here we add the ℚ-linear structure
(`c • f` computed in `A`) and the duality `(M, e)^* = (M^*, e^*)`, `f ↦ f^*`.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

namespace HSP

open DualCat

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A]

namespace Karoubi

/-- Scalar multiplication on morphisms of `Kar A`, computed in `A`. -/
instance instSMulHom {P Q : Karoubi A} : SMul ℚ (P ⟶ Q) where
  smul c f := ⟨c • f.f, by rw [Linear.smul_comp, Linear.comp_smul, f.comm]⟩

@[simp]
lemma smul_f {P Q : Karoubi A} (c : ℚ) (f : P ⟶ Q) : (c • f).f = c • f.f := rfl

/-- The ℚ-linear structure on `Kar A`. -/
instance instLinear : Linear ℚ (Karoubi A) where
  homModule P Q :=
    Function.Injective.module ℚ (Idempotents.Karoubi.inclusionHom P Q)
      (fun f g h => Idempotents.Karoubi.hom_ext f g h) (fun _ _ => rfl)
  smul_comp P Q R c f g := Idempotents.Karoubi.hom_ext _ _ (by simp)
  comp_smul P Q R f c g := Idempotents.Karoubi.hom_ext _ _ (by simp)

end Karoubi

omit [Linear ℚ A] in
private lemma sub_f {P Q : Karoubi A} (a b : P ⟶ Q) : (a - b).f = a.f - b.f :=
  map_sub (Idempotents.Karoubi.inclusionHom P Q) a b

variable [HasFiniteBiproducts A] [DualCat A]

/-- The duality on `Kar A`: `(M, e)^* = (M^*, e^*)` and `f ↦ f^*`. It makes `Kar A` a duality
category. -/
instance instDualCatKaroubi : DualCat (Karoubi A) where
  dual P := ⟨dual P.X, dualHom P.p, by rw [← dualHom_comp, P.idem]⟩
  dualHom f := ⟨dualHom f.f, by
    simp only [← dualHom_comp, Category.assoc, f.comm]⟩
  dualHom_id P := rfl
  dualHom_comp f g := Idempotents.Karoubi.hom_ext _ _ (dualHom_comp _ _)
  dualHom_add f g := Idempotents.Karoubi.hom_ext _ _ (dualHom_add _ _)
  dualHom_smul c f := Idempotents.Karoubi.hom_ext _ _ (dualHom_smul _ _)
  dual_dual P := Idempotents.Karoubi.ext (dual_dual P.X) (by simp [dualHom_dualHom])
  dualHom_dualHom f := Idempotents.Karoubi.hom_ext _ _ (by simp [dualHom_dualHom])
  dualHom_zero := Idempotents.Karoubi.hom_ext _ _ dualHom_zero
  dualHom_neg f := Idempotents.Karoubi.hom_ext _ _ (dualHom_neg _)
  dualHom_sub f g := Idempotents.Karoubi.hom_ext _ _ (by
    simp only [sub_f]; exact dualHom_sub _ _)
  dualHom_eqToHom h := by subst h; exact Idempotents.Karoubi.hom_ext _ _ (by simp)

namespace Karoubi

@[simp]
lemma dual_X (P : Karoubi A) : (dual P).X = dual P.X := rfl

@[simp]
lemma dual_p (P : Karoubi A) : (dual P).p = dualHom P.p := rfl

@[simp]
lemma dualHom_f {P Q : Karoubi A} (f : P ⟶ Q) : (dualHom f).f = dualHom f.f := rfl

end Karoubi

end HSP
