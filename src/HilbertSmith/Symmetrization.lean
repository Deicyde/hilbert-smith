import Mathlib
import HilbertSmith.TransposeInvolution

namespace HilbertSmith

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]

variable (d : Duality C) [d.D.Additive]

/-- Halves of `α` plus its transpose are symmetric when doubling is
injective on forms. -/
theorem Duality.symmetrization (h : d.IsInvolutive) {X : C}
    (half_uniq : ∀ a b : X ⟶ d.D.obj (op X), a + a = b + b → a = b)
    (α τ : X ⟶ d.D.obj (op X)) (hτ : τ + τ = α + d.transpose α) :
    d.transpose τ = τ := by
  apply half_uniq
  have h1 := congrArg d.transpose hτ
  rw [d.transpose_add, d.transpose_add, d.transpose_transpose h] at h1
  rw [h1, hτ, add_comm (d.transpose α) α]

end HilbertSmith
