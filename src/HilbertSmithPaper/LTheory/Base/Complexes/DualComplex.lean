import HilbertSmithPaper.LTheory.Base.Categories.KaroubiDuality

/-!
# Dual complex

Complexes are `ℤ`-graded chain complexes `ChainComplex B ℤ` in a duality category `B`. For a
complex `C` and `n : ℤ`, the dual complex `C^{n-*}` has `(C^{n-*})_r = (C_{n-r})^*` and
differential `d_r = (-1)^r d^*`. A chain map `f : C ⟶ D` gives `f^{n-*} : D^{n-*} ⟶ C^{n-*}`,
`(f^{n-*})_r = (f_{n-r})^*`.

This module also records that a duality category has binary biproducts
(`DualCat.hasBinaryBiproducts`), so that mapping cones and sums of complexes are available.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

/-- A duality category has binary biproducts (Mathlib does not derive them from finite
biproducts by instance); used for mapping cones and sums of complexes. -/
instance (priority := 100) DualCat.hasBinaryBiproducts : HasBinaryBiproducts B :=
  hasBinaryBiproducts_of_finite_biproducts B

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

/-- The dual `f^{n-*} : D^{n-*} ⟶ C^{n-*}` of a chain map `f : C ⟶ D`,
`(f^{n-*})_r = (f_{n-r})^*`. -/
@[simps]
def dualCx.map {C D : ChainComplex B ℤ} (f : C ⟶ D) (n : ℤ) : dualCx D n ⟶ dualCx C n where
  f r := dualHom (f.f (n - r))
  comm' i j _ := by
    change dualHom (f.f (n - i)) ≫ (i.negOnePow • dualHom (C.d (n - j) (n - i))) =
      (i.negOnePow • dualHom (D.d (n - j) (n - i))) ≫ dualHom (f.f (n - j))
    rw [Linear.comp_units_smul, Linear.units_smul_comp, ← dualHom_comp, ← dualHom_comp, f.comm]

end HSP
