import Mathlib
import HilbertSmithPaper.Categories.Asymptotic.AsymptoticCategory

/-!
# The empty sequence

The empty sequence `(0, ∅)` of `𝒜_𝐆(X)`: rank `0` at every level (`HSP.AsymPre.zero`).
-/

namespace HSP

variable {p : ℕ} {G : GroupSeq p} {X : Type*}

/-- The empty sequence: rank `0` at every level. -/
def AsymPre.zero : AsymPre G X where
  n _ := 0
  x _ := Fin.elim0

end HSP
