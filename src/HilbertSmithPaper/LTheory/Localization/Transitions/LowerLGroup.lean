import Mathlib
import HilbertSmithPaper.LTheory.Base.Groups.LGroup
import HilbertSmithPaper.LTheory.Bounded.Categories.IteratedBoundedCategory
import HilbertSmithPaper.LTheory.Base.Groups.ProjectiveLGroup

/-!
# Lower L-group

For `j : ℕ` (the stage: the number of bounded directions) and `k : ℤ`,
`L^{⟨-j⟩}_k(A) = L^p_{k+j}(C_{ℤ^j} A)`, with `C_{ℤ^j} A = BoundedPow A j`. At stage `0` this is
`L^p_k(A)` (`lowerL_zero`; `BoundedPow A 0` is `A` by definition, and `k + 0 = k`).
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v u

/-- **Lower L-group.** `L^{⟨-j⟩}_k(A) = L^p_{k+j}(C_{ℤ^j} A)`. -/
noncomputable abbrev lowerL (A : Type u) [Category.{v} A] [Preadditive A] [Linear ℚ A]
    [HasFiniteBiproducts A] [DualCat A] (j : ℕ) (k : ℤ) : Type (max u v) :=
  Lp (BoundedPow A j) (k + j)

/-- At stage `0` the lower L-group is the projective L-group. -/
lemma lowerL_zero (A : Type u) [Category.{v} A] [Preadditive A] [Linear ℚ A]
    [HasFiniteBiproducts A] [DualCat A] (k : ℤ) : lowerL A 0 k = Lp A k := by
  simp only [lowerL, Nat.cast_zero, add_zero]
  rfl

end HSP
