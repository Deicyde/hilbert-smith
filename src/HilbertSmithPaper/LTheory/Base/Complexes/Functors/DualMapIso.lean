import HilbertSmithPaper.LTheory.Base.Complexes.Functors.DualMapComp
import HilbertSmithPaper.LTheory.Base.Complexes.Functors.DualMapId

/-!
# Dual of an isomorphism of complexes

An isomorphism of complexes `u : C ≅ D` gives an isomorphism `u^{n-*} : D^{n-*} ≅ C^{n-*}`,
with inverse `(u⁻¹)^{n-*}`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

/-- **Dual of an isomorphism of complexes.** The dual `u^{n-*}` of an isomorphism of complexes `u : C ≅ D`, an isomorphism
`D^{n-*} ≅ C^{n-*}`. -/
@[simps]
def dualCx.mapIso {C D : ChainComplex B ℤ} (u : C ≅ D) (n : ℤ) : dualCx D n ≅ dualCx C n where
  hom := dualCx.map u.hom n
  inv := dualCx.map u.inv n
  hom_inv_id := by rw [← dualCx.map_comp, u.inv_hom_id, dualCx.map_id]
  inv_hom_id := by rw [← dualCx.map_comp, u.hom_inv_id, dualCx.map_id]

end HSP
