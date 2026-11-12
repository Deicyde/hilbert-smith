import HilbertSmithPaper.LTheory.Base.Pairs.CobordismEquivalence
import HilbertSmithPaper.LTheory.Base.Categories.KaroubiDuality

/-!
# L-group

For a duality category `B`, `L_k(B)` is the set of cobordism classes `[C, φ]` of strict
`k`-dimensional symmetric Poincaré complexes in `B`: the quotient of `SymPoincare B k` by the
equivalence relation `Cobordant` (an equivalence relation by `cobordant_equivalence`).
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

namespace HSP

universe v u

/-- Cobordism as a setoid on strict `k`-dimensional symmetric Poincaré complexes. -/
instance SymPoincare.cobordismSetoid (B : Type u) [Category.{v} B] [Preadditive B] [Linear ℚ B]
    [HasFiniteBiproducts B] [DualCat B] (k : ℤ) : Setoid (SymPoincare B k) :=
  ⟨Cobordant, cobordant_equivalence B k⟩

/-- The L-group `L_k(B)`: cobordism classes of strict `k`-dimensional symmetric Poincaré
complexes in the duality category `B`. -/
def LGroup (B : Type u) [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
    [DualCat B] (k : ℤ) : Type (max u v) :=
  Quotient (SymPoincare.cobordismSetoid B k)

/-- The class `[C, φ] ∈ L_k(B)`. -/
def LGroup.mk {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
    [DualCat B] {k : ℤ} (x : SymPoincare B k) : LGroup B k :=
  Quotient.mk _ x

end HSP
