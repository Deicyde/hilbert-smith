import HilbertSmithPaper.LTheory.Ultimate.Groups.UltimateLGroup
import HilbertSmithPaper.Categories.Asymptotic.FreeCategory
import HilbertSmithPaper.Categories.Asymptotic.GroupSequence

/-!
# Point comparison for the free categories

For a group sequence `(G_i, χ_i)`, `cls : L^p_k(Free(ℚ[G_i])) → 𝕃_k(Free(ℚ[G_i]))` is bijective
for all `k` and `i`.

This rests on the open statement Lemma U, through Lemma U passes to the blocks.
-/

namespace HSP

/-- `cls : L^p_k(Free(ℚ[G_i])) → 𝕃_k(Free(ℚ[G_i]))` is bijective. -/
theorem cls_bijective_free {p : ℕ} (G : GroupSeq p) (i : ℕ) (k : ℤ) :
    Function.Bijective (cls (FreeCat (G.G i)) k) := by
  sorry

end HSP
