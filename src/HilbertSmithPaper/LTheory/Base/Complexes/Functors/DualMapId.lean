import HilbertSmithPaper.LTheory.Base.Complexes.Functors.DualMap

/-!
# Duals of identity chain maps

`(1_C)^{n-*} = 1`, componentwise from `1^* = 1`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

/-- **Duals of identity chain maps.** `(1_C)^{n-*} = 1`. -/
lemma dualCx.map_id (C : ChainComplex B ℤ) (n : ℤ) : dualCx.map (𝟙 C) n = 𝟙 (dualCx C n) := by
  ext r
  simp

end HSP
