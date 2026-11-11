import Mathlib
import HilbertSmithPaper.Categories.Asymptotic.GroupSequence

/-!
# The trivial group sequence

The trivial group sequence `𝟏` (`HSP.GroupSeq.trivial p`): every `G_i` is the one-point group, and
every `χ_i` is zero. Its groups are the one-point type `Unit`, with the corresponding `Unique`
instance.
-/

namespace HSP

/-- **The trivial group sequence** `𝟏`: every `G_i` is the trivial group. -/
def GroupSeq.trivial (p : ℕ) : GroupSeq p where
  G _ := Unit
  χ _ := 0

instance (p i : ℕ) : Unique ((GroupSeq.trivial p).G i) := inferInstanceAs (Unique Unit)

end HSP
