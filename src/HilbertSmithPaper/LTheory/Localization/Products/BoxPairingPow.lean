import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.BoxDual

/-!
# Box product on iterated bounded categories

For `B = C_{ℤ^j} A`, the box product pairing `Kar B × C_ℤ(ℚ) → Kar C_ℤ(B)` has target
`Kar C_{ℤ^{j+1}} A`, since `C_{ℤ^{j+1}} A = C_ℤ(C_{ℤ^j} A)` by definition.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

namespace HSP

universe v u

/-- **Box product on iterated bounded categories.** The box product pairing
`Kar C_{ℤ^j} A × C_ℤ(ℚ) → Kar C_{ℤ^{j+1}} A`. -/
noncomputable abbrev boxPairingPow (A : Type u) [Category.{v} A] [Preadditive A] [Linear ℚ A]
    [HasFiniteBiproducts A] [DualCat A] (j : ℕ) :
    DualityPairing (Karoubi (BoundedPow A j)) (Bounded FreeQ) (Karoubi (BoundedPow A (j + 1))) :=
  boxPairing

end HSP
