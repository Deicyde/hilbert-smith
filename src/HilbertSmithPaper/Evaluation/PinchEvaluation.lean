import HilbertSmithPaper.Corner.Theorem.ScalarIteratedCut
import HilbertSmithPaper.Evaluation.ConstantCp2Sequence
import HilbertSmithPaper.Evaluation.CubicalPinch
import HilbertSmithPaper.Evaluation.Germ
import HilbertSmithPaper.Categories.Asymptotic.PointQuotientFunctor

/-!
# Evaluation at the cubical pinch

For `n ≥ 1`, `R > 0` and `0 < s < R/√n`, the scalar iterated cut `Δ_𝟏` sends the labelled-model
class of the cubical pinch `κ` to `ε q_* cls [𝐏]`, `ε = (-1)^{n(n+1)/2}`, where `𝐏` is the
constant sequence of `CP²` in `𝒫_𝟏` and `q : 𝒫_𝟏 → 𝒱_𝟏` the quotient functor. The labelled-model
class is formed from a local datum `A` at the prime `p`.
-/

open CategoryTheory HSP.ChainModels

namespace HSP.Evaluation

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- **Evaluation at the cubical pinch**: `Δ_𝟏 𝔪_κ = ε q_* cls [𝐏]`, `ε = (-1)^{n(n+1)/2}`. -/
theorem iterCut_pinch (A : LocalDatum p n D ρplus) (R s : ℝ) (hn : 1 ≤ n) (hR : 0 < R)
    (hs : 0 < s) (hs' : s < R / √n) :
    Corner.scalarIteratedCut p n R s hn hR hs hs' (germ A R (cubicalPinch n s hs)) =
      ((-1 : ℤ) ^ (n * (n + 1) / 2)) •
        ultL.map (VCat.q (GroupSeq.trivial p)) 4
          (cls _ 4 (LGroup.mk ((cp2Seq p).map (karEmb _)))) := by
  sorry

end HSP.Evaluation
