import Mathlib

/-!
# Mapping cone

For a chain map `g : C ⟶ D` of `ℤ`-graded chain complexes in a preadditive category with binary
biproducts, the mapping cone has `cone g _r = D_r ⊞ C_{r-1}` and differential
`d (x, y) = (d x + (-1)^{r-1} g y, d y)`. This is the paper's sign convention, which differs
from Mathlib's `homotopyCofiber`.

In Lean the differential `d i j` is defined for all `i j`; it is the formula above when
`i - 1 = j` and zero otherwise, and `D.XIsoOfEq` transports `D_{i-1}` to `D_j`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v u

variable {V : Type u} [Category.{v} V] [Preadditive V] [HasBinaryBiproducts V]
  {C D : ChainComplex V ℤ}

namespace cone

/-- The differential of the mapping cone: `d (x, y) = (d x + (-1)^{i-1} g y, d y)` from degree
`i` to degree `j = i - 1`, and zero otherwise. -/
noncomputable def d (g : C ⟶ D) (i j : ℤ) :
    (D.X i ⊞ C.X (i - 1)) ⟶ (D.X j ⊞ C.X (j - 1)) :=
  if h : i - 1 = j then
    biprod.lift (biprod.fst ≫ D.d i j + (i - 1).negOnePow • (biprod.snd ≫ g.f (i - 1) ≫
      (D.XIsoOfEq h).hom)) (biprod.snd ≫ C.d (i - 1) (j - 1))
  else 0

end cone

/-- The mapping cone `𝒞(g)` of a chain map `g : C ⟶ D`: `𝒞(g)_r = D_r ⊞ C_{r-1}`,
`d (x, y) = (d x + (-1)^{r-1} g y, d y)`. -/
noncomputable abbrev cone (g : C ⟶ D) : ChainComplex V ℤ where
  X r := D.X r ⊞ C.X (r - 1)
  d := cone.d g
  shape i j hij := by
    simp only [ComplexShape.down_Rel] at hij
    unfold cone.d
    split_ifs with h
    · exact absurd (by omega) hij
    · rfl
  d_comp_d' i j k hij hjk := by
    simp only [ComplexShape.down_Rel] at hij hjk
    have h1 : i - 1 = j := by omega
    have h2 : j - 1 = k := by omega
    subst h1 h2
    ext <;> simp [cone.d, Preadditive.comp_add, Preadditive.add_comp, Int.negOnePow_sub]

end HSP
