import HilbertSmithPaper.LTheory.Base.Pairs.Cobordism

/-!
# Cobordism is an equivalence relation

Cobordism of strict `k`-dimensional symmetric Poincaré complexes in a duality category is
reflexive, symmetric and transitive.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v u

/-- Cobordism of strict `k`-dimensional symmetric Poincaré complexes is an equivalence
relation. -/
theorem cobordant_equivalence (B : Type u) [Category.{v} B] [Preadditive B] [Linear ℚ B]
    [HasFiniteBiproducts B] [DualCat B] (k : ℤ) :
    Equivalence (Cobordant : SymPoincare B k → SymPoincare B k → Prop) := by
  sorry

end HSP
