import Mathlib
import HilbertSmithPaper.LTheory.Base.Categories.DualityCategory
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.BasedCategory

/-!
# Based vector spaces

The duality on the category `ℚ` of based vector spaces (`HSP.FreeQ`) is `(ℚ^d)^* = ℚ^d` and
`g^* = gᵀ`, so `M^{**} = M` and `g^{**} = g` hold by definition.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

namespace FreeQ

/-- **Based vector spaces.** The duality on `ℚ`: `(ℚ^d)^* = ℚ^d` and `g^* = gᵀ`. -/
instance instDualCat : DualCat FreeQ where
  dual X := X
  dualHom f := ofMatrix (toMatrix f).transpose
  dualHom_id X := Matrix.transpose_one
  dualHom_comp f g := Matrix.transpose_mul (toMatrix g) (toMatrix f)
  dualHom_add f g := Matrix.transpose_add (toMatrix f) (toMatrix g)
  dualHom_smul c f := Matrix.transpose_smul c (toMatrix f)
  dual_dual X := rfl
  dualHom_dualHom f := by simp
  dualHom_zero := Matrix.transpose_zero
  dualHom_neg f := Matrix.transpose_neg (toMatrix f)
  dualHom_sub f g := Matrix.transpose_sub (toMatrix f) (toMatrix g)
  dualHom_eqToHom h := by subst h; exact Matrix.transpose_one

@[simp]
lemma dual_eq (X : FreeQ) : DualCat.dual X = X := rfl

@[simp]
lemma dualHom_toMatrix {X Y : FreeQ} (f : X ⟶ Y) :
    toMatrix (DualCat.dualHom f) = (toMatrix f).transpose := rfl

/-- Non-vacuity of the duality-category interface: `ℚ` is a duality category. -/
private theorem dualCat_nonempty : Nonempty (DualCat FreeQ) := ⟨inferInstance⟩

end FreeQ

end HSP
