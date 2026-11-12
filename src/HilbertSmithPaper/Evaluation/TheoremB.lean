import Mathlib
import HilbertSmithPaper.Evaluation.Germ
import HilbertSmithPaper.Evaluation.CubicalPinch
import HilbertSmithPaper.Corner.Theorem.ScalarIteratedCut
import HilbertSmithPaper.Signatures.Tail.TailSignature
import HilbertSmithPaper.Evaluation.GermHomotopy
import HilbertSmithPaper.Evaluation.PinchEvaluation
import HilbertSmithPaper.Evaluation.ConstantTail

/-!
# Theorem B

Let `n ≥ 1`, `R > 0` and `0 < s < R/√n`, let `κ : 𝕋ⁿ → Sⁿ` be the cubical pinch for `n` and `s`,
`𝔪` the labelled-model class for `n` and `R`, and `Δ_𝟏` the scalar iterated cut for `n`, `R` and
`s`. There is `ε ∈ {±1}`, depending only on `n`, such that for every continuous `c : 𝕋ⁿ → Sⁿ`
homotopic to `κ`, `σ_tail(Δ_𝟏 𝔪_c) = [(ε, ε, …)] ∈ ℤ^ℕ ⧸ ℤ^(ℕ)`.

This rests on the open statements lifting, the two sides of an excision boundary, and Lemma U.

Proof: `𝔪_c = 𝔪_κ` (homotopic labellings), `Δ_𝟏 𝔪_κ = ε q_* cls[𝐏]` with `ε = (-1)^{n(n+1)/2}`
(evaluation at the cubical pinch), and `σ_tail(q_* cls[𝐏]) = [(1, 1, …)]` (constant tail).

## Encoding

`theoremB n hn` (the declaration of the article). `ε` is chosen before the prime `p`, the radii
`R`, `s`, the local datum `A` (from which the chain models of `𝔪` are built) and `c`, so it depends
only on `n`. `ℤ^ℕ ⧸ ℤ^(ℕ)` is `Filter.Germ Filter.cofinite ℤ`, and `[(ε, ε, …)]` the germ of the
constant sequence `ε`.
-/

open HSP.ChainModels

namespace HSP.Evaluation

/-- **Theorem B.** For `c` homotopic to the cubical pinch, `σ_tail(Δ_𝟏 𝔪_c) = [(ε, ε, …)]`, with
`ε = ±1` depending only on `n`. -/
theorem theoremB (n : ℕ) (hn : 1 ≤ n) : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
    ∀ (p : ℕ) [Fact p.Prime] {D ρplus R s : ℝ} (hR : 0 < R) (hs : 0 < s) (hs' : s < R / √n)
      (A : LocalDatum p n D ρplus) (c : C(Torus n, Corner.RoundSphere n)),
      c.Homotopic (cubicalPinch n s hs) →
      tailSign (GroupSeq.trivial p) (Corner.scalarIteratedCut p n R s hn hR hs hs' (germ A R c)) =
        ((fun _ : ℕ => ε) : Filter.Germ Filter.cofinite ℤ) := by
  refine ⟨(-1 : ℤ) ^ (n * (n + 1) / 2), neg_one_pow_eq_or ℤ _, fun p _ D ρplus R s hR hs hs' A c hc => ?_⟩
  rw [germ_eq_of_homotopic A R hc, iterCut_pinch A R s hn hR hs hs', map_zsmul, tailSign_const,
    ← Filter.Germ.coe_smul]
  congr 1
  funext i
  simp

end HSP.Evaluation
