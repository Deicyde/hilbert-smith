import Mathlib
import HilbertSmithPaper.Signatures.LFour.ComplexSignature
import HilbertSmithPaper.LTheory.Base.Pairs.PoincarePair

/-!
# Boundaries have zero signature

If `(C, φ)` is the boundary of a strict `5`-dimensional symmetric Poincaré pair in
`Kar Free(ℚ[G])`, then `Sign_G(C, φ) = 0` (`HSP.complexSign_boundary`).
-/

open CategoryTheory CategoryTheory.Idempotents

namespace HSP

variable {G : Type} [AddGroup G] [Fintype G] [DecidableEq G]

/-- The boundary of a strict `5`-dimensional Poincaré pair has signature zero. -/
theorem complexSign_boundary (W : SymPair (Karoubi (FreeCat G)) 4 5) :
    complexSign W.boundary = 0 := by
  sorry

end HSP
