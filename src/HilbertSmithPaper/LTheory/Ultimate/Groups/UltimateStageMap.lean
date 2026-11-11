import HilbertSmithPaper.LTheory.Ultimate.Groups.UltimateLGroup

/-!
# Stage maps into the ultimate L-group

`ι_j : L^{⟨-j⟩}_k(A) → 𝕃_k(A)` is the map from stage `j` of the sequence of lower L-groups into
its colimit.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v u

variable (A : Type u) [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]

/-- The map `ι_j : L^{⟨-j⟩}_k(A) → 𝕃_k(A)` from stage `j` of the colimit. -/
noncomputable def ultL.of (k : ℤ) (j : ℕ) : lowerL A j k →+ ultL A k :=
  (colimit.ι (lowerLSeq A k) j).hom

end HSP
