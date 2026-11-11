import Mathlib

/-!
# Signs for tensor products of chain complexes

For chain complexes indexed by `ℤ` (`ComplexShape.down ℤ`, differentials of degree `-1`), the
sign of `1 ⊠ d` on `C_p ⊠ D_q` in a tensor product of complexes is `ε p = (-1)^p`. This is the
instance `TensorSigns (ComplexShape.down ℤ)` used by Mathlib's total complexes.
-/

namespace HSP

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The signs `ε p = (-1)^p` on `ℤ` for chain complexes (`ComplexShape.down ℤ`): the sign of
`1 ⊠ d` on `C_p ⊠ D_q` in a tensor product of complexes. -/
instance tensorSignsDownInt : ComplexShape.TensorSigns (ComplexShape.down ℤ) where
  ε' := MonoidHom.mk' Int.negOnePow Int.negOnePow_add
  rel_add p q r (hpq : q + 1 = p) := by simp only [ComplexShape.down_Rel]; lia
  add_rel p q r (hpq : q + 1 = p) := by simp only [ComplexShape.down_Rel]; lia
  ε'_succ := by
    rintro _ q rfl
    dsimp
    rw [Int.negOnePow_succ, neg_neg]

end HSP
