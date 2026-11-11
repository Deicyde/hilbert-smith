import HilbertSmithPaper.LTheory.Ultimate.Groups.UltimateLGroup

/-!
# Every element comes from a finite stage

Every element of `𝕃_k(A)` is `ι_j x` for some `j ≥ 0` and some `x ∈ L^{⟨-j⟩}_k(A)`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v u

variable (A : Type u) [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]

/-- Every element of `𝕃_k(A)` is `ι_j x` for some stage `j`. -/
theorem ultL.exists_of (k : ℤ) (y : ultL A k) :
    ∃ (j : ℕ) (x : lowerL A j k), ultL.of A k j x = y := by
  have : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{max u v}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  exact Concrete.colimit_exists_rep (lowerLSeq A k) y

end HSP
