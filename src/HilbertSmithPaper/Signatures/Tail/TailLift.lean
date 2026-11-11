import HilbertSmithPaper.LTheory.Ultimate.Groups.InducedMap
import HilbertSmithPaper.Categories.Asymptotic.PointQuotientFunctor

/-!
# Classes over `𝒱` lift

Let `𝐆` be a group sequence, `𝒫_𝐆` its sequence category and `q : 𝒫_𝐆 → 𝒱_𝐆` the quotient
functor onto its point category. Every `x ∈ 𝕃_4(𝒱_𝐆)` is `q_* y` for some `y ∈ 𝕃_4(𝒫_𝐆)`.

This rests on the open statements Lemma U, through coordinates detect `𝕃_3(𝒮)`, and lifting,
through the ultimate boundary of the point filtration.
-/

namespace HSP

/-- Every class of `𝕃_4(𝒱_𝐆)` is `q_* y` for some `y ∈ 𝕃_4(𝒫_𝐆)`. -/
theorem tail_lift {p : ℕ} (G : GroupSeq p) (x : ultL (VCat G) 4) :
    ∃ y : ultL (PCat G) 4, ultL.map (VCat.q G) 4 y = x := by
  sorry

end HSP
