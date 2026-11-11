import HilbertSmithPaper.LTheory.Ultimate.Groups.InducedMap

/-!
# Identity on ultimate L

`(id_A)_* = id` on `𝕃_k(A)`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]

/-- `(id_A)_* = id` on `𝕃_k(A)`. -/
theorem ultL.map_id (k : ℤ) : ultL.map (DualFunctor.id A) k = AddMonoidHom.id _ := by
  sorry

end HSP
