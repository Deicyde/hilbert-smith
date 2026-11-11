import HilbertSmithPaper.LTheory.Ultimate.Groups.InducedMap
import HilbertSmithPaper.LTheory.Base.Categories.UnitaryIsomorphism

/-!
# Unitary invariance on ultimate L

If `η : F ≅ G` is a unitary natural isomorphism of duality functors `A → B`, then `F_* = G_*` on
`𝕃_k(A)`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]
  {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

/-- A unitary natural isomorphism `F ≅ G` gives `F_* = G_*` on `𝕃_k(A)`. -/
theorem ultL.map_eq_of_unitaryIso {F G : DualFunctor A B} (η : DualFunctor.UnitaryIso F G)
    (k : ℤ) : ultL.map F k = ultL.map G k := by
  sorry

end HSP
