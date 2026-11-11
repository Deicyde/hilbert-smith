import HilbertSmithPaper.LTheory.Base.Complexes.DualComplex

/-!
# Dual of a chain map

A chain map `f : C ⟶ D` gives `f^{n-*} : D^{n-*} ⟶ C^{n-*}`, `(f^{n-*})_r = (f_{n-r})^*`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

/-- **Dual of a chain map.** The dual `f^{n-*} : D^{n-*} ⟶ C^{n-*}` of a chain map `f : C ⟶ D`,
`(f^{n-*})_r = (f_{n-r})^*`. -/
@[simps]
def dualCx.map {C D : ChainComplex B ℤ} (f : C ⟶ D) (n : ℤ) : dualCx D n ⟶ dualCx C n where
  f r := dualHom (f.f (n - r))
  comm' i j _ := by
    change dualHom (f.f (n - i)) ≫ (i.negOnePow • dualHom (C.d (n - j) (n - i))) =
      (i.negOnePow • dualHom (D.d (n - j) (n - i))) ≫ dualHom (f.f (n - j))
    rw [Linear.comp_units_smul, Linear.units_smul_comp, ← dualHom_comp, ← dualHom_comp, f.comm]

end HSP
