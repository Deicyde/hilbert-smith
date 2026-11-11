import HilbertSmithPaper.LTheory.Base.Pairs.SumOfPoincare
import HilbertSmithPaper.LTheory.Base.Pairs.Cobordism

/-!
# Sum of Poincaré complexes up to cobordism

Up to cobordism, the sum of strict `k`-dimensional symmetric Poincaré complexes is compatible
with cobordism, negation is compatible with cobordism, and the sum is associative and
commutative, with unit `(0, 0)` and inverse `(C, -φ)`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

/-- The laws of the sum of strict symmetric Poincaré complexes up to cobordism. -/
theorem cobordant_sum_laws {k : ℤ} :
    (∀ x x' y y' : SymPoincare B k, Cobordant x x' → Cobordant y y' →
      Cobordant (x.sum y) (x'.sum y')) ∧
    (∀ x y : SymPoincare B k, Cobordant x y → Cobordant x.neg y.neg) ∧
    (∀ x y z : SymPoincare B k, Cobordant ((x.sum y).sum z) (x.sum (y.sum z))) ∧
    (∀ x y : SymPoincare B k, Cobordant (x.sum y) (y.sum x)) ∧
    (∀ x : SymPoincare B k, Cobordant ((SymPoincare.zero k).sum x) x) ∧
    (∀ x : SymPoincare B k, Cobordant (x.neg.sum x) (SymPoincare.zero k)) := by
  sorry

end HSP
