import Mathlib
import HilbertSmithPaper.Signatures.LFour.MiddleForm
import HilbertSmithPaper.Signatures.Real.RealCohomologyAction

/-!
# The middle form is nonsingular, symmetric and invariant

For a strict `4`-dimensional symmetric Poincaré complex `(C, φ)` in `Kar Free(ℚ[G])`, the middle
form `b_C` on `H^2(C; ℝ)` is symmetric and nondegenerate, and `G` acts on `H^2(C; ℝ)` by
`b_C`-isometries (`HSP.middleForm_nonsingular`).
-/

open CategoryTheory CategoryTheory.Idempotents

namespace HSP

variable {G : Type} [AddGroup G] [Fintype G] [DecidableEq G]

/-- The middle form is symmetric and nondegenerate, and `G` acts by isometries. -/
theorem middleForm_nonsingular (x : SymPoincare (Karoubi (FreeCat G)) 4) :
    (middleForm x).IsSymm ∧ (middleForm x).Nondegenerate ∧
      ∀ (g : Multiplicative G) (a b : realHco x.C 2),
        middleForm x (realHco.rep g a) (realHco.rep g b) = middleForm x a b := by
  sorry

end HSP
