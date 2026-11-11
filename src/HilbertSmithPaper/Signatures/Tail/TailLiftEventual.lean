import HilbertSmithPaper.LTheory.Ultimate.Groups.InducedMap
import HilbertSmithPaper.Categories.Asymptotic.PointQuotient

/-!
# Lifts agree eventually

Let `𝐆` be a group sequence, with sequence category `𝒫_𝐆`, coordinate functors
`π_i : 𝒫_𝐆 → Free(ℚ[G_i])` and quotient functor `q : 𝒫_𝐆 → 𝒱_𝐆` onto the point category. If
`y, y' ∈ 𝕃_4(𝒫_𝐆)` and `q_* y = q_* y'`, then `(π_i)_* y = (π_i)_* y'` in
`𝕃_4(Free(ℚ[G_i]))` for all but finitely many `i`.

This rests on the open statements Lemma U, through classes in `𝕃_4(𝒮)` have finite support, and
lifting, through ultimate exactness in the middle.
-/

namespace HSP

/-- If `q_* y = q_* y'` then `(π_i)_* y = (π_i)_* y'` for all but finitely many `i`. -/
theorem tail_lift_eventually {p : ℕ} (G : GroupSeq p) (y y' : ultL (PCat G) 4)
    (h : ultL.map (VCat.q G) 4 y = ultL.map (VCat.q G) 4 y') :
    ∀ᶠ i in Filter.cofinite, ultL.map (PCat.proj G i) 4 y = ultL.map (PCat.proj G i) 4 y' := by
  sorry

end HSP
