import HilbertSmithPaper.LTheory.Base.Categories.DualityCategory
import HilbertSmithPaper.LTheory.Base.Categories.DualBinaryBiproducts

/-!
# Dual complex

Complexes are `ℤ`-graded chain complexes `ChainComplex B ℤ` in a duality category `B`. For a
complex `C` and `n : ℤ`, the dual complex `C^{n-*}` has `(C^{n-*})_r = (C_{n-r})^*` and
differential `d_r = (-1)^r d^*`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

/-- The dual complex `C^{n-*}`: `(C^{n-*})_r = (C_{n-r})^*`, with differential
`(-1)^i (d^C_{n-j, n-i})^*` from degree `i` to degree `j`. -/
@[simps]
abbrev dualCx (C : ChainComplex B ℤ) (n : ℤ) : ChainComplex B ℤ where
  X r := dual (C.X (n - r))
  d i j := i.negOnePow • dualHom (C.d (n - j) (n - i))
  shape i j hij := by
    rw [C.shape, dualHom_zero, smul_zero]
    simp only [ComplexShape.down_Rel] at hij ⊢
    omega
  d_comp_d' i j k _ _ := by
    simp only [Linear.units_smul_comp, Linear.comp_units_smul, ← dualHom_comp,
      C.d_comp_d, dualHom_zero, smul_zero]

end HSP
