import Mathlib
import HilbertSmithPaper.LTheory.Base.Complexes.DualComplex

/-!
# Dual complexes have finitely many nonzero chain objects

For a complex `C` in a duality category with finitely many chain objects that are not zero
objects, and `m ∈ ℤ`, the dual complex `C^{m-*}` has finitely many nonzero chain objects: its
chain object in degree `r` is `C_{m-r}^*`, and the dual of a zero object is a zero object.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]

private lemma isZero_dual {X : A} (h : IsZero X) : IsZero (dual X) := by
  rw [IsZero.iff_id_eq_zero] at h ⊢
  rw [← dualHom_id, h, dualHom_zero]

/-- **Dual complexes have finitely many nonzero chain objects.** -/
lemma dualCx_finite {C : ChainComplex A ℤ} (hC : {r | ¬ IsZero (C.X r)}.Finite) (m : ℤ) :
    {r | ¬ IsZero ((dualCx C m).X r)}.Finite := by
  refine (hC.image fun r => m - r).subset ?_
  intro r hr
  exact ⟨m - r, fun hz => hr (isZero_dual hz), by ring⟩

end HSP
