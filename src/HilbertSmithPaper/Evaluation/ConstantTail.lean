import HilbertSmithPaper.Evaluation.ConstantCp2Sequence
import HilbertSmithPaper.Signatures.Tail.TailSignature
import HilbertSmithPaper.LTheory.Base.Categories.KaroubiEmbedding

/-!
# Constant tail

Let `𝐏 ∈ 𝒫_𝟏` be the constant sequence `(P, φ_P)` in the sequence category of the trivial group
sequence, and `q` the quotient functor to the point category. Then
`σ_tail(q_* cls[𝐏]) = [(1, 1, …)]`, where `cls[𝐏]` is `cls` of the image of `𝐏` under the Karoubi
embedding `M ↦ (M, 1)`.

This rests on the open statements Lemma U and lifting, through the tail signature.
-/

namespace HSP.Evaluation

/-- `σ_tail(q_* cls[𝐏]) = [(1, 1, …)]`. -/
theorem tailSign_const (p : ℕ) :
    tailSign (GroupSeq.trivial p)
        (ultL.map (VCat.q _) 4 (cls _ 4 (LGroup.mk ((cp2Seq p).map (karEmb _))))) =
      ((fun _ => 1 : ℕ → ℤ) : Filter.Germ (Filter.cofinite : Filter ℕ) ℤ) := by
  sorry

end HSP.Evaluation
