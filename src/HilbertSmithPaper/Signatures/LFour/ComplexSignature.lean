import Mathlib
import HilbertSmithPaper.Signatures.LFour.MiddleFormNonsingular
import HilbertSmithPaper.Signatures.Forms.FormSignature

/-!
# Signature of a complex

For a strict `4`-dimensional symmetric Poincaré complex `(C, φ)` in `Kar Free(ℚ[G])`,
`Sign_G(C, φ) = sign_{b_C} : G → ℝ` (`HSP.complexSign`), the equivariant signature of the middle
form with the permutation action of `G` on `H^2(C; ℝ)`. Since `G` is written additively, the
signature of forms is taken for `Multiplicative G`, at `ofAdd g`.
-/

open CategoryTheory CategoryTheory.Idempotents

namespace HSP

variable {G : Type} [AddGroup G] [Fintype G] [DecidableEq G]

/-- **The signature of a complex**, `Sign_G(C, φ) = sign_{b_C} : G → ℝ`. -/
noncomputable def complexSign (x : SymPoincare (Karoubi (FreeCat G)) 4) (g : G) : ℝ :=
  formSign (middleForm x) realHco.rep (Multiplicative.ofAdd g)

end HSP
