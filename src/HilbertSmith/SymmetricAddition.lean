import Mathlib
import HilbertSmith.TransposeInvolution

namespace HilbertSmith

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]

variable (d : Duality C) [d.D.Additive]

/-- The transpose preserves negation. -/
theorem Duality.transpose_neg {X : C} (α : X ⟶ d.D.obj (op X)) :
    d.transpose (-α) = -d.transpose α := by
  unfold Duality.transpose
  rw [op_neg, d.D.map_neg, Preadditive.comp_neg]

/-- The zero form is symmetric. -/
theorem Duality.symmetric_zero {X : C} :
    d.IsSymmetric (0 : X ⟶ d.D.obj (op X)) := by
  unfold Duality.IsSymmetric
  exact d.transpose_zero.symm

/-- Sums of symmetric forms are symmetric. -/
theorem Duality.symmetric_add {X : C} {α β : X ⟶ d.D.obj (op X)}
    (hα : d.IsSymmetric α) (hβ : d.IsSymmetric β) :
    d.IsSymmetric (α + β) := by
  unfold Duality.IsSymmetric at hα hβ ⊢
  rw [d.transpose_add, ← hα, ← hβ]

/-- Negations of symmetric forms are symmetric. -/
theorem Duality.symmetric_neg {X : C} {α : X ⟶ d.D.obj (op X)}
    (hα : d.IsSymmetric α) : d.IsSymmetric (-α) := by
  unfold Duality.IsSymmetric at hα ⊢
  rw [d.transpose_neg, ← hα]

end HilbertSmith
